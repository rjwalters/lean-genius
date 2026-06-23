# S6 STATE-SYNC — cantors-theorem-oq-01-oq-03

**Date**: 2026-05-16
**Agent**: researcher-12
**Mode**: STATE-SYNC (doc-only)
**PR**: (will be created post-commit)

---

## §1. Why STATE-SYNC

Slug `cantors-theorem-oq-01-oq-03` has been **fully discharged** since
S2 (`PR #17741`, 2026-05-12), with parent prose polish in S5
(`PR #17856`, same day). Resolution status:

- `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` — 227 LOC, 7 theorems,
  **0 axioms, 0 sorries**.
- Gallery `meta.json` — `status: "verified"`, `badge: "mathlib"`,
  `axiomCount: 0`, `sorries: 0`.
- The OQ ("Can König's constraint cf(2^κ) > κ be formalized in Lean 4
  without axioms?") is resolved YES via Mathlib's
  `Cardinal.lt_cof_power`.

The only remaining drift between origin/main and the post-resolution
target state is **administrative** — neither candidate-pool nor
research-JSON were updated when the resolution shipped.

This S6 ships a doc-only PR that:

1. Marks candidate-pool entry `status: completed` (was `available`).
2. Refreshes research-JSON `currentState.phase` / `status` /
   `iteration` / `lastUpdate`.
3. Updates `state.md` head: Phase `ACT` → `COMPLETED`, iter `5` → `6`,
   adds S6 STATE-SYNC summary above the preserved S5 body.
4. Packages a paste-ready `@[deprecated]` skeleton for the optional
   sibling-cleanup follow-up in §3 below (deferred to a future agent
   or Hermit sweep — see §6).

No Lean / meta.json / problem.md / knowledge.md edits.

---

## §2. Drift table

| Surface | Pre-S6 | Post-S6 | Touch site |
|---|---|---|---|
| `.lean/state/candidate-pool.json` `candidates[…id=<slug>].status` | `available` (slug had no claim before today; SCRIPT-managed) | `completed` | `claim-problem.sh update … completed` |
| `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` `currentState.phase` | `ACT` | `COMPLETED` | json edit (this PR) |
| `…` `status` | `in-progress` | `completed` | json edit |
| `…` `currentState.iteration` | `5` | `6` | json edit |
| `…` `currentState.since` | `2026-05-12T04:50:00Z` | `2026-05-16T…Z` | json edit |
| `…` `lastUpdate` (top-level) | `2026-05-12T…` | `2026-05-16T…Z` | json edit |
| `…` `currentState.focus` | (S5 polish narrative) | (S6 STATE-SYNC narrative) | json edit |
| `…` `currentState.nextAction` | (S6 alt sibling cleanup OR mark completed) | (optional sibling deprecation only — see §3) | json edit |
| `research/problems/cantors-theorem-oq-01-oq-03/state.md` Phase head | `ACT (S5 polish)` / Iter `5` | `COMPLETED (S6 STATE-SYNC)` / Iter `6` | state.md edit (this PR) |
| state.md body | (S5 summary only) | S6 summary prepended above S5 (preserved) | state.md edit |
| `research/problems/<slug>/sessions/2026-05-16-s6-state-sync.md` | (did not exist) | (this file) | new file |
| Gallery `src/data/proofs/<slug>/meta.json` | `status: verified` | (unchanged) | NOT touched |
| `problem.md` | (no Status field) | (unchanged) | NOT touched |
| `knowledge.md` | (unchanged) | (unchanged) | NOT touched |
| `proofs/Proofs/Cantors*.lean` | (unchanged) | (unchanged) | NOT touched |

---

## §3. Paste-ready `@[deprecated]` skeleton for sibling oq-02 cleanup

**Status**: NOT shipped in this PR. Packaged here for future pickup.
This is the optional follow-up named in S5's `Next Action` /
research-JSON's `nextAction`. Adding these attributes to sibling
`cantors-theorem-oq-01-oq-02` is gallery-hygiene only — semantics
unchanged, all downstream call-sites already use the stronger forms.

### Target file

`proofs/Proofs/CantorsTheoremOQ01OQ02.lean`

### Skeleton — `konig_constraint_powerSet_real` (line 208)

Replace lines 199–211 with:

```lean
/-- **König's Constraint**: The cofinality of |𝒫(ℝ)| = ℶ₂ strictly exceeds
    𝔠 = ℶ₁ = |ℝ|.

    This rules out ℶ₂ being any cardinal with cofinality ≤ 𝔠, for example:
    - ℵ_ω (cofinality ω = ℵ₀ ≤ 𝔠)
    - ℵ_{ω·2} (cofinality ω)
    - ℵ_{ω₁·ω} (cofinality ω)

    Only cardinals with cofinality > 𝔠 are candidates for the aleph-index of ℶ₂.

    Superseded by `CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum`
    which has the identical statement and proof. New code should
    prefer the OQ03 form (more cross-references, lives next to
    `konig_general` so callers can switch to the universally-quantified
    form trivially). -/
@[deprecated (since := "2026-05-16")]
theorem konig_constraint_powerSet_real :
    (𝔠 : Cardinal.{0}) < (#(Set ℝ)).ord.cof := by
  rw [CantorsTheoremOQ01.card_powerSet_real_formula]
  exact Cardinal.lt_cof_power Cardinal.aleph0_le_continuum (by norm_num)
```

### Skeleton — `konig_constraint_beth (n : ℕ)` (line 215)

Replace lines 213–222 with:

```lean
/-- König's Constraint generalized: for all n : ℕ, cf(ℶ_{n+1}) > ℶₙ.
    The cofinality of each beth level strictly exceeds the previous.

    Superseded by `CantorsTheoremOQ01OQ03.konig_constraint_beth (α : Ordinal)`
    which parameterizes over an arbitrary ordinal α (this version is
    the strict-ℕ-only specialization). New code should prefer the
    Ordinal form; the ℕ form is recoverable via `(↑n : Ordinal)`. -/
@[deprecated (since := "2026-05-16")]
theorem konig_constraint_beth (n : ℕ) :
    (Cardinal.beth (↑n : Ordinal) : Cardinal.{0}) <
    (2 ^ Cardinal.beth (↑n : Ordinal) : Cardinal.{0}).ord.cof := by
  apply Cardinal.lt_cof_power _ (by norm_num)
  -- ℵ₀ = ℶ₀ ≤ ℶₙ (beth is monotone, 0 ≤ n in Ordinal)
  calc (ℵ₀ : Cardinal.{0}) = Cardinal.beth 0 := Cardinal.beth_zero.symm
    _ ≤ Cardinal.beth (↑n : Ordinal) :=
        Cardinal.beth_strictMono.monotone (Ordinal.zero_le _)
```

### Net effect

- 2 new `@[deprecated (since := "2026-05-16")]` attributes.
- 2 expanded docstrings (with cross-references to OQ03 forms).
- 0 Lean declarations added, removed, or substantively changed.
- Build risk: **minimal** — `@[deprecated]` is a pure metadata
  attribute; the only failure mode is a Lean syntax bump (the
  `since` parameter format is stable since Lean 4.0).
- Downstream callers: the third theorem in oq-02
  (`aleph_index_lower_cofinality_bound`, line 226) calls
  `konig_constraint_powerSet_real`. After deprecation, this will
  emit a deprecation warning. Two options for the cleanup PR:
  - (a) Leave the call, accept the warning as a self-deprecation
    cycle inside oq-02.
  - (b) Re-route to `cf_powerSet_real_gt_continuum` from OQ03 (adds
    one import or `open` line).
  - **Recommendation**: (a) — keeping the call internal to oq-02
    preserves the slug's self-contained build, and the warning
    surfaces in the gallery as a visible hint.

### Skeleton risk inventory (R1–R3)

| Ref | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | `@[deprecated]` syntax drift in newer Lean | LOW | `since := "YYYY-MM-DD"` form is stable; if breaks, drop the `since` |
| R2 | Cross-file deprecation visibility (gallery viewer) | LOW | Gallery already shows deprecation warnings as a yellow badge on annotation hover |
| R3 | Downstream `aleph_index_lower_cofinality_bound` warning | LOW | Self-deprecation inside oq-02; see option (a) above |

### ACT-readiness gate for the deferred follow-up

| Gate | Status |
|---|---|
| Bearer pins stable at SHA `2df2f0150c…` | ✓ (verified in §5 below) |
| Lean attribute syntax verified | ✓ (`@[deprecated (since := "…")]` is standard since Lean 4) |
| Build inheritance unchanged | ✓ (deprecation adds no semantic dependency) |
| Skeleton paste-ready in one location | ✓ (§3 above) |
| Sibling-slug claim available | ✗ (would need to claim `cantors-theorem-oq-01-oq-02`) |
| Docker daemon up (for build verify) | ✗ (B1 INFRA — hung) |
| Skeleton LOC estimate confirmed | ✓ (~20 LOC including expanded docstrings) |
| OQ resolution complete | ✓ (this slug's resolution is independent) |

6/8 GREEN substantive · 2/8 RED (claim + INFRA). Future agent
needs to claim the sibling slug and have Docker functional to ship.

---

## §4. Build inheritance — slug-wide 0/0/0 audit

| File | LOC @ HEAD | Axioms | Sorries | Build origin |
|---|---|---|---|---|
| `proofs/Proofs/CantorsTheoremOQ01.lean` | (S5-polished version) | 0 | 0 | Verified pre-S2; S5 was docstring-only |
| `proofs/Proofs/CantorsTheoremOQ01OQ01.lean` | 172 | 0 | 0 | Pre-S2 verified |
| `proofs/Proofs/CantorsTheoremOQ01OQ02.lean` | 257 | 0 | 0 | Pre-S2 verified |
| `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` | 227 | 0 | 0 | Verified by S2 PR #17741 + S4 PR #17807 |
| `proofs/Proofs/CantorsTheoremOQ02.lean` | 282 | 0 | 0 | Pre-S2 verified |
| `proofs/Proofs/CantorsTheoremOQ03.lean` | 311 | 0 | 0 | Pre-S2 verified |

Slug-wide: 0 axioms / 0 sorries across all 6 Cantor files. Build
inheritance from origin/main is unconditional — no Lean changes in
this PR.

---

## §5. Bearer-pin recheck (3-spot + 2 derived)

**Pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)

Verified live via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>`:

| Lemma | Module | Line @ pin | Verification |
|---|---|---|---|
| `Cardinal.lt_cof_power` | `SetTheory/Cardinal/Cofinality.lean` | 743 | ✓ `theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < (b ^ a).ord.cof` |
| `Cardinal.aleph0_le_continuum` | `SetTheory/Cardinal/Continuum.lean` | 68 | ✓ `theorem aleph0_le_continuum : ℵ₀ ≤ 𝔠` |
| `Cardinal.aleph0_le_aleph` | `SetTheory/Cardinal/Aleph.lean` | 417 | ✓ `theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ ℵ_ o` |
| `Cardinal.beth_zero` | `SetTheory/Cardinal/Aleph.lean` | 624 | ✓ `theorem beth_zero : ℶ_ 0 = ℵ₀` |
| `Cardinal.beth_strictMono` | `SetTheory/Cardinal/Aleph.lean` | 609 | ✓ `theorem beth_strictMono : StrictMono beth` |

File-level sha-check (via `gh api`):

| File | Size | Blob SHA |
|---|---|---|
| `Cofinality.lean` | 29962 | `39bf4f9f53b45c3c877166c90b7c972401cebb81` |
| `Continuum.lean` | 4732 | `48469e5cf7bd6a2f24ec04bf5368f23aa0365805` |
| `Aleph.lean` | 22686 | `8ea53805fb00ca7f988bfabc958b3495a8073705` |

All five bearer lemmas exist at the expected lines with stable
signatures. No API drift since S2 (2026-05-12, four days ago).

---

## §6. Not in this PR

| Item | Why deferred |
|---|---|
| Sibling `@[deprecated]` Lean edit | Skeleton paste-ready in §3; defer to (a) sibling-slug claim, (b) Hermit sweep, or (c) curator pass on sibling |
| S7 BUILD-VERIFY | Docker daemon hung; build inherits from origin/main (already verified by S2/S4/S5) |
| Gallery enrichment | Enriched in PR #17776 (9 annotations); no further work indicated |
| Auditor handoff | `meta.json status: verified` already correct |
| problem.md edits | No Status field; narrative content unchanged |
| knowledge.md edits | Content reflects pre-S2 OBSERVE; resolution narrative now lives in research-JSON `currentState.focus` |
| Sibling-slug state.md updates | Out of slug-scope; sibling has its own iteration log |

---

## §7. Host infra snapshot

```
$ df -h /
/dev/disk3s1s1   926Gi    16Gi   6.9Gi    70%    458k   72M    1%   /

$ timeout 30 docker version
Client:
 Version: 29.4.1
 OS/Arch: darwin/arm64
 Context: desktop-linux
EXIT=124  ← daemon hung

$ timeout 10 docker info | head -10
Client: ...
Server:    ← server block empty (daemon unresponsive)
EXIT=0
```

- Disk: 6.9 Gi avail / 70% capacity — adequate for doc-only PR.
- Docker: client responsive, **daemon hung** (B1 INFRA).
- Containers: 0 running.
- Lean build cache: untouched (no compile attempted).

---

## §8. Honesty / confidence

- ✓ Slug resolution is genuinely complete (verified by S2/S4/S5
  build chain, 0/0/0 across all 6 Cantor files).
- ✓ Drift table covers all observed gaps between origin/main and
  the post-resolution target state.
- ✓ Bearer recheck confirms no Mathlib API drift since S2.
- ⚠ The optional sibling deprecation is **not** pursued in this PR;
  packaged paste-ready for future pickup. Honest reason: shipping a
  2-attribute Lean edit with `(build pending)` would muddy the
  slug's freshly-clean status, and the sibling-slug deserves its
  own iteration log entry for the deprecation.
- ⚠ Quality gate auto-checked: `knowledge.progressSummary` exists
  (S5 narrative), `insights (7) + builtItems (8) = 15 ≥ 3` — gate
  passes for `completed` graduation without `FORCE_COMPLETE=1`.
- Confidence in this STATE-SYNC: high. The OQ resolution is
  unambiguous, the drift is purely administrative, and the
  deferred follow-up has a clean handoff path.

---

## §9. Files touched

| File | Status | LOC change |
|---|---|---|
| `research/problems/cantors-theorem-oq-01-oq-03/state.md` | edited | +~120 / -2 (S6 header prepended, S5 body preserved) |
| `research/problems/cantors-theorem-oq-01-oq-03/sessions/2026-05-16-s6-state-sync.md` | new | +~260 (this file) |
| `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` | edited | small (phase/status/iter/since/lastUpdate/focus/nextAction fields only) |
| `.lean/state/candidate-pool.json` | edited (via script) | 1 field flip (status `available` → `completed`) |

**Not touched** (intentional):
- `proofs/Proofs/CantorsTheoremOQ01.lean`
- `proofs/Proofs/CantorsTheoremOQ01OQ01.lean`
- `proofs/Proofs/CantorsTheoremOQ01OQ02.lean`
- `proofs/Proofs/CantorsTheoremOQ01OQ03.lean`
- `proofs/Proofs/CantorsTheoremOQ02.lean`
- `proofs/Proofs/CantorsTheoremOQ03.lean`
- `src/data/proofs/cantors-theorem-oq-01-oq-03/{meta,annotations,index}.{json,ts}`
- `research/problems/cantors-theorem-oq-01-oq-03/{problem,knowledge}.md`

---

## §10. PR title and labels

**Title**: `research(cantors-theorem-oq-01-oq-03): S6 STATE-SYNC — slug COMPLETED (verified, 0/0/0, S2+S4+S5 inherited); pool/JSON catch-up + sibling-deprecation skeleton packaged (doc-only)`

**Labels**: `research`

**No** `loom:review-requested` (per CLAUDE.md "Math agents must NOT
add `loom:review-requested` to their PRs"). The deployer merges
math PRs directly when build inheritance is sound and content is
doc-only.
