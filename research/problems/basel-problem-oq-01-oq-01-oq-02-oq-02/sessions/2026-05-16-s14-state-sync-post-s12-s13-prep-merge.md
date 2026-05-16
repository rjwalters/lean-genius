## Session 2026-05-16 (Session 14 STATE-SYNC) — post-S12+S13-PREP-merge state-sync, bearer drift recheck (0 drift), two ACT-time risk flags pre-discharged

**Mode**: PREP / STATE-SYNC (documentation-only)
**Outcome**: progress (no Lean changes; no sorry/axiom delta; refreshes
state.md and JSON deferred from PR #19217 (S12 PREP) and PR #19299 (S13
PREP), both of which left state.md/JSON refresh "owned by next
STATE-SYNC iteration" while #19017 (S11 BUILD-REPAIR) was still open at
their write time)

### TL;DR

Both PR #19217 (S12 PREP, researcher-12) and PR #19299 (S13 PREP,
researcher-3) merged in the 2026-05-15T18:00–18:06Z drain wave (within
~5 minutes of each other and ~5 minutes after PR #19017 (S11
BUILD-REPAIR) merged at 17:55–17:59Z). Both PREPs explicitly deferred
`state.md` / JSON refresh to "next STATE-SYNC iteration" to remain
strictly conflict-free with the open S11 PR. This S14 ships that
deferred refresh:

1. **Bearer drift recheck (0 drift)**: all six Mathlib bearers pinned by
   S12+S13 at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   are re-verified at the same SHA (which is still current on
   origin/main as of `lake-manifest.json` HEAD `d35a6f0f2ac29b3519e5`,
   2026-05-16T00:08:48Z). Zero file-position changes. See §3.
2. **Two S13 §3.6 ACT-time risk flags PRE-DISCHARGED**: the two unpinned
   bearers flagged for ACT-time verification (`Nat.coprime_iff_isRelPrime`
   and `Nat.factorization_eq_zero_of_not_prime`) are pin-located at
   exact line numbers in the current Mathlib SHA. See §4. This removes
   the only two open risk items from the S15 ACT readiness checklist.
3. **One additional bearer NEWLY pinned**: `isRelPrime_one_left` at
   `Mathlib/Algebra/Divisibility/Units.lean:166`, used in S13 §3.4
   sub-case (i). S13 PREP wrote "Mathlib pin needed; at
   `Mathlib/Algebra/GroupWithZero/Coprime.lean` or similar"; the actual
   location is `Mathlib/Algebra/Divisibility/Units.lean`. See §5.
4. **S12+S13 compatibility synthesis**: the two PREPs reached
   compatible (not contradictory) recommendations. S12 picked Path
   (A.1) → S12 ACT. S13 audited S12's bearer choices, validated them,
   added one missing bearer (`Finset.prod_dvd_of_isRelPrime`), and
   sequenced the post-merge work as S14 ACT (A.1) → S15 ACT (A.2).
   This STATE-SYNC RENUMBERS that sequence by +1 to absorb itself:
   **S15 ACT = A.1, S16 ACT = A.2**. See §6.
5. **State.md/JSON delta**: state.md gains a "Session 14 STATE-SYNC"
   header documenting the renumber and the bearer-recheck. JSON gains
   `iteration: 14`, refreshed `lastUpdate`, refreshed `nextAction`,
   and three new entries each in `knowledge.insights` and
   `knowledge.nextSteps`. No `builtItems` change (PREPs add no Lean).

### §1 Status snapshot at PREP-write time

**Date**: 2026-05-16 (UTC) / 2026-05-15 (PT). Both S12+S13 PREP files
are dated 2026-05-15 (PT); this S14 STATE-SYNC is dated 2026-05-16
(UTC) since the wrapper fired post-midnight UTC.

**This slug's open PRs** (`gh pr list -R rjwalters/lean-genius
--search 'basel-problem-oq-01-oq-01-oq-02-oq-02 in:title' --state
open`):

- (none) — all of #19017 (S11 BUILD-REPAIR), #19217 (S12 PREP), and
  #19299 (S13 PREP) merged in the 2026-05-15T18:00–18:06Z drain wave.

**Recent merges on this slug** (`gh pr list -R rjwalters/lean-genius
--search 'basel-problem-oq-01-oq-01-oq-02-oq-02 in:title' --state
merged --limit 3`):

| PR # | Title (truncated) | Merged at |
|------|--------------------|-----------|
| #19299 | S13 PREP — sibling audit of #19217 | 2026-05-15T18:00:43Z |
| #19217 | S12 PREP — coordination + Path (A)/(B) bearer audit | 2026-05-15T18:05:45Z |
| #19017 | S11 BUILD-REPAIR — Mathlib v4.26.0 9-edit kit | 2026-05-15T17:59:27Z (approx) |

(S13 merged BEFORE S12 by ~5 minutes despite the lower iteration
number — drain-wave ordering is auto and uncorrelated with iteration
sequence; both are doc-only and the order is harmless.)

**System-wide deployer state**: 77 open PRs (down from 387 at S13 PREP
write time, ~7h prior). Last main merge `#19327`
(`fix(mechanic): mean-value-theorem-...`) at 2026-05-16T00:08:33Z
(~23 minutes ago). 3 commits in the last 10 minutes; 0 in the last
2 minutes. Drain wave has tapered. The 6.5h gap between S13 PREP write
(2026-05-15T10:14Z) and the deployer drain wave start
(2026-05-15T17:55Z, when #19017 merged) confirms the deployer-stall
pattern resolved on its own.

**Bearer slug state** (`grep -c "axiom \|sorry" proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`):
0 axioms, 0 sorries (unchanged from S11 post-fix Docker-verified state).
File LOC 799 (unchanged).

### §2 What S12+S13 PREPs deferred to "next STATE-SYNC"

Both PREPs ship under explicit "Conflict-free" clauses to avoid editing
state.md/JSON while a sibling PR was still open:

#### §2.1 S12 PREP §"Coordination scope" (lines 16–22 of S12 PREP)

> This S12 PREP is **conflict-free**: it adds exactly one new file
> (this report) and does **not** touch `state.md`,
> `src/data/research/problems/<slug>.json`, or
> `BaselProblemOQ01OQ01OQ02OQ02.lean`. PR #19017 owns the post-S11
> refresh of those three files; this PREP supplements it with a
> pre-ACT audit of paths the merged state.md leaves open ((A) Kummer,
> (B) vdP §6 bypass, (D) partial vdP audit).

#### §2.2 S13 PREP §6.3 "Conflict-free assertions" (lines 743–751)

> This PREP adds exactly ONE new file:
> `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-15-s13-prep-sibling-audit-of-s12-paths-ab.md`.
>
> - Different from #19017's modified files (Lean + state.md + JSON).
> - Different from #19217's added file (S12 PREP session, different
>   filename, different day-stamp tag).
> - No git-merge conflict with either PR's diff.

#### §2.3 What this STATE-SYNC therefore owns

- `state.md`: append "Session 14 STATE-SYNC" section near the top
  (above Session 11) capturing S12 + S13 outcomes + this STATE-SYNC's
  bearer drift recheck.
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json`:
  refresh `currentState.iteration` (11 → 14), `currentState.since`
  (2026-05-08 → 2026-05-16), `currentState.focus`,
  `currentState.nextAction`, `lastUpdate`. Add three entries each to
  `knowledge.insights` and `knowledge.nextSteps`.

### §3 Bearer drift recheck — 6 bearers, 0 drift since S13 PREP write

All six bearers verified by direct download of the file at the
lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=${SHA}`
+ `xargs curl -sL`. The SHA is identical to S13 PREP's pin SHA
(re-confirmed against current `proofs/lake-manifest.json` HEAD).

| # | Bearer | Path | Line | First pinned by |
|---|--------|------|------|-----------------|
| 1 | `Nat.pow_factorization_choose_le` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 196 | S12 PREP §3 + §"S12 ACT skeleton" |
| 2 | `Nat.prod_pow_factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 267 | S12 PREP §"S12 ACT skeleton" |
| 3 | `Nat.Prime.emultiplicity_choose` | `Mathlib/Data/Nat/Multiplicity.lean` | 209 | S13 PREP §"Distinct value" #4 |
| 4 | `Nat.Prime.emultiplicity_factorial` | `Mathlib/Data/Nat/Multiplicity.lean` | 102 | S13 PREP §"Distinct value" #4 |
| 5 | `Finset.prod_dvd_of_isRelPrime` | `Mathlib/RingTheory/Coprime/Lemmas.lean` | 252 | S13 PREP §2.4 |
| 6 | `DecompositionMonoid` instance via `[Nonempty (GCDMonoid α)]` | `Mathlib/Algebra/GCDMonoid/Basic.lean` | 493 | S13 PREP §2.5 |

#### §3.1 Reproducibility commands (S14 STATE-SYNC pin verification)

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# §3 bearer #1 + #2 — Choose/Factorization.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Choose/Factorization.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '190,210p;260,275p'
# Confirms: line 196 pow_factorization_choose_le, line 267 prod_pow_factorization_choose

# §3 bearer #3 + #4 — Multiplicity.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Multiplicity.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '95,110p;205,220p'
# Confirms: line 102 emultiplicity_factorial, line 209 emultiplicity_choose

# §3 bearer #5 — Coprime/Lemmas.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Coprime/Lemmas.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '245,265p'
# Confirms: line 252 Finset.prod_dvd_of_isRelPrime

# §3 bearer #6 — GCDMonoid/Basic.lean
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/GCDMonoid/Basic.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '485,500p'
# Confirms: line 493 instance [Nonempty (GCDMonoid α)] : DecompositionMonoid α
```

#### §3.2 Why a SAME-SHA recheck still has value

The lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is
unchanged in `proofs/lake-manifest.json` since e4c0464b1c5
(S11 BUILD-REPAIR merged 2026-05-14T17:59Z), so a "drift" check at the
file level returns 0 changes. The value of this re-pin is:

1. **Confirms bearer surface stability across the 6 PRs merged on this
   slug since S13 PREP write**: PRs #19017, #19217, #19299 (this slug)
   plus 50+ system-wide PRs in the drain wave. None of those touched
   the lake manifest, so Mathlib bearer pins are stable.
2. **Documents the recheck protocol** for future S15 ACT and beyond:
   any session that consumes a bearer should re-pin under the
   then-current `lake-manifest.json` SHA before claiming the bearer is
   in scope. The "false-blocked-on-upstream-Mathlib" trap from
   `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md`
   is averted by re-pinning at lake SHA, not at Mathlib HEAD.
3. **Catches the case where an S15 ACT iteration would land on a
   different lake SHA**: if a future Mathlib bump lands between this
   STATE-SYNC and S15 ACT, the recheck protocol surfaces the new SHA
   and triggers re-verification. This S14 establishes the SHA pin as a
   gate for S15 ACT readiness.

### §4 ACT-time risk flags from S13 §3.6 — PRE-DISCHARGED

S13 PREP §3.6 listed two ACT-time risk flags (Mathlib bearers that
S13 referenced but did not pin to exact line numbers):

| Risk flag | Mitigation declared by S13 | Status under S14 |
|-----------|----------------------------|------------------|
| `Nat.coprime_iff_isRelPrime` may have moved or renamed in v4.26.0 | "Confirm at ACT time after #19017 merges" | **PRE-DISCHARGED**: pinned at `Mathlib/Data/Nat/GCD/Basic.lean:218` (§4.1) |
| `factorization_eq_zero_of_not_prime` may have renamed in v4.26.0 | "Cross-check #19017's edit kit at merge time" | **PRE-DISCHARGED**: pinned at `Mathlib/Data/Nat/Factorization/Defs.lean:129` (§4.2) |

#### §4.1 `Nat.coprime_iff_isRelPrime` pin

Direct file fetch (same SHA) confirms:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/GCD/Basic.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '215,225p'
```

Output:

```lean
-- line 218
theorem coprime_iff_isRelPrime {m n : ℕ} : m.Coprime n ↔ IsRelPrime m n := by
```

Signature matches S13 §3.4's `(Nat.coprime_iff_isRelPrime).mp hcopw`
call. Bearer is in scope after `import Mathlib.Data.Nat.GCD.Basic`,
which is already transitively imported via
`Mathlib.Algebra.GCDMonoid.Finset` (the file's first import).

#### §4.2 `Nat.factorization_eq_zero_of_not_prime` pin

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Factorization/Defs.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '125,135p'
```

Output:

```lean
-- line 129
theorem factorization_eq_zero_of_not_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := by
```

Signature matches S13 §3.3 Case B's contrapositive use:
`absurd ((Nat.choose n k).factorization_eq_zero_of_not_prime h) hv_pos.ne'`.
Note S13 wrote it as `Nat.factorization_eq_zero_of_not_prime` but the
Mathlib name in the `Nat` namespace is just `factorization_eq_zero_of_not_prime`
(the file lives in `Mathlib/Data/Nat/Factorization/Defs.lean` inside
`namespace Nat`). When called as a method on `(Nat.choose n k).factorization`,
both forms resolve identically — no S15 ACT adjustment needed.

#### §4.3 Discharge note for S15 ACT

Both bearers in scope and pin-verified at the slug's `lake-manifest.json`
SHA. S15 ACT can implement the §3.3 Case B and §3.4 sub-case (i) skeletons
verbatim from S13 PREP without further bearer audit.

### §5 New bearer NEWLY pinned — `isRelPrime_one_left`

S13 §3.4 sub-case (i) used `isRelPrime_one_left : IsRelPrime 1 x` and
flagged "(Mathlib pin needed; at `Mathlib/Algebra/GroupWithZero/Coprime.lean`
or similar)". The actual location is **`Mathlib/Algebra/Divisibility/Units.lean:166`**.

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Divisibility/Units.lean?ref=${SHA}" \
  -q '.download_url' | xargs curl -sL | sed -n '165,168p'
```

Output:

```lean
-- line 166
theorem isRelPrime_one_left : IsRelPrime 1 x := isUnit_one.isRelPrime_left
theorem isRelPrime_one_right : IsRelPrime x 1 := isUnit_one.isRelPrime_right
```

`Mathlib/Algebra/Divisibility/Units.lean` is transitively imported via
`Mathlib/RingTheory/Coprime/Basic.lean` (which imports `Mathlib/Algebra/GroupWithZero/Units/Lemmas.lean`
which imports `Mathlib/Algebra/GroupWithZero/Units/Basic.lean` which imports
the Divisibility/Units file). It is in scope after the standard
`import Mathlib.Tactic` already in the slug's Lean file (line 2:
`import Mathlib.Tactic`).

**S13 §3.4 update**: replace "(Mathlib pin needed; at
`Mathlib/Algebra/GroupWithZero/Coprime.lean` or similar)" with
"(`Mathlib/Algebra/Divisibility/Units.lean:166`)". Both pinned name
and signature are correct as written in S13.

### §6 S12+S13 compatibility synthesis — unified S15+S16 ACT plan

S12 and S13 reach **compatible (non-contradictory)** conclusions on
both Path (A) and Path (B):

| Topic | S12 PREP conclusion | S13 PREP conclusion | Compatible? |
|-------|---------------------|---------------------|-------------|
| Path (A) Kummer is the right route | Yes (§"Recommendation": queue S12 ACT as A.1) | Yes (§5 + §3 elaborate the skeleton) | ✓ |
| Path (B) vdP §6 bypass viability | Rejected (induction-on-k closed form does not bypass) | Rejected (re-validates S12's algebra; W-Z not in Mathlib) | ✓ |
| A.1 LOC budget | ~50-60 LOC | ~30-40 LOC (S13 §3.5 reconciliation) | ✓ — S13 tighter |
| A.2 LOC budget | ~80-120 LOC | (deferred to S15 in S13's plan) | ✓ |
| Mathlib bearer for `Finset.prod` step | "Or `Finset.prod_dvd via primes-coprime`" (loose) | `Finset.prod_dvd_of_isRelPrime` at `Lemmas.lean:252` (precise) | ✓ — S13 sharpens |
| `DecompositionMonoid ℕ` typeclass dependency | Not surfaced | `Mathlib/Algebra/GCDMonoid/Basic.lean:493` instance via `Nonempty (GCDMonoid ℕ)` | ✓ — S13 catches |
| Recommended next ACT scope | S12a: prove `choose_dvd_lcmRange` (~60 LOC) | S14 ACT: A.1 = `choose_dvd_lcmRange` (~30-40 LOC); S15 ACT: A.2 (~80-120 LOC) | ✓ |

#### §6.1 Renumbering: S15 ACT = A.1, S16 ACT = A.2

S13 §7 sequenced the post-merge ACTs as **S14 ACT (A.1)** and **S15 ACT
(A.2)**. This S14 STATE-SYNC ITERATES the iteration counter to 14
(absorbing itself into the sequence), so the post-STATE-SYNC ACT
numbering shifts by +1:

- ~~S14 ACT~~ → **S15 ACT**: A.1 implementation (`choose_dvd_lcmRange`,
  ~30-40 LOC, Docker-verify required).
- ~~S15 ACT~~ → **S16 ACT**: A.2 implementation (`mul_choose_dvd_lcmRange`,
  ~80-120 LOC, Docker-verify required).
- ~~S16+ ACT~~ → **S17+ ACT**: apply A.2 to the vdP §6 alternating-bilinear
  summand for the final `denominator_control` discharge.

The renumber preserves the *content* sequence; only labels shift.

#### §6.2 S15 ACT readiness checklist (post-discharge S13 §3.6)

| Item | Status |
|------|--------|
| `Nat.pow_factorization_choose_le` bearer pinned | ✓ S12 + S13 |
| `Nat.prod_pow_factorization_choose` bearer pinned | ✓ S12 + S13 |
| `Finset.prod_dvd_of_isRelPrime` bearer pinned | ✓ S13 §2.4 |
| `DecompositionMonoid ℕ` typeclass in scope | ✓ S13 §2.5 (instance at GCDMonoid/Basic.lean:493) |
| `Nat.coprime_iff_isRelPrime` bearer pinned | ✓ **S14 §4.1 (was S13 §3.6 risk flag)** |
| `Nat.factorization_eq_zero_of_not_prime` bearer pinned | ✓ **S14 §4.2 (was S13 §3.6 risk flag)** |
| `isRelPrime_one_left` bearer pinned | ✓ **S14 §5 (newly pinned)** |
| Lake SHA stable (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | ✓ S14 §3 |
| File LOC + axiom + sorry count baseline known | ✓ 799 / 0 / 0 (S11 post-fix) |
| Build-pending precedent for ACT — IMPORTANT | **Docker-verify required** (S11 §"Build-pending watchlist" admonition) |

S15 ACT can begin without further PREP work. The S13 §3 + §3.5 LOC
budget of ~30-40 LOC is the binding constraint; if Docker-verification
is reachable in a single ~14-minute round, the iteration is feasible
within a normal session window.

#### §6.3 S16 ACT (A.2) staging — early bearer audit

S13 §5 estimated A.2 at ~80-120 LOC and identified the technical heart
as the bound `v_p(m · C(n,m)) ≤ ⌊log_p n⌋`. S13 §5.1 numerically
ruled out the naive `v_p(n) + ⌊log_p(n-1)⌋ ≤ ⌊log_p n⌋` route at
(n,m,p) = (4,2,2), and S13 §5 surfaced two bearers for the correct
Legendre route:

- `Nat.Prime.emultiplicity_choose` at `Multiplicity.lean:209` (Kummer's
  theorem in `emultiplicity` form)
- `Nat.Prime.emultiplicity_factorial` at `Multiplicity.lean:102`
  (Legendre's formula)

Both pinned (S14 §3 #3, #4, 0 drift). The A.2 ACT skeleton needs one
additional bridge: connecting `emultiplicity` (the `ℕ∞`-valued form
used by Mathlib's Kummer/Legendre theorems) with `factorization` (the
`ℕ`-valued `Finsupp p ↦ v_p(n)` form used by S15 A.1's
`pow_factorization_choose_le`). The standard bridge is
`Nat.factorization_eq_emultiplicity` or `Nat.Prime.emultiplicity_eq_factorization`
at `Mathlib/Data/Nat/Factorization/Defs.lean`. **Pin deferred to S16
ACT** since S15 (A.1) does not need it; staging here as a pre-S16
flag.

### §7 Conflict-free assertions

This S14 STATE-SYNC modifies exactly three files:

1. **NEW**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-16-s14-state-sync-post-s12-s13-prep-merge.md`
   (this file).
2. **MODIFIED**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02/state.md`
   — appends a "Session 14 STATE-SYNC" section near the top (above
   Session 11), preserves all prior session content verbatim.
3. **MODIFIED**: `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json`
   — refreshes `currentState.iteration` (11 → 14),
   `currentState.since`, `currentState.focus`, `currentState.nextAction`,
   `lastUpdate`; adds 3 entries each to `knowledge.insights` and
   `knowledge.nextSteps`. No `builtItems` change. No `references`
   change (the bearers are documented in the session note + state.md).

**No Lean changes**. **No `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`
edits**. **No sibling file edits**.

#### §7.1 Open-PR conflict surface (this slug)

At PREP-write time: 0 open PRs on this exact slug (per §1). The 2
open PRs returned by the broader `basel-problem-oq-01-oq-01-oq-02`
search (#17551, #17619) are for the **sibling slug
`basel-problem-oq-01-oq-01-oq-02-oq-03`** (last component `oq-03`,
not `oq-02`); they touch `BaselProblemOQ01OQ01OQ02OQ03.lean` not
`BaselProblemOQ01OQ01OQ02OQ02.lean`. **No git-merge conflict.**

#### §7.2 Open-PR conflict surface (other slugs touching JSON)

The JSON file `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-02.json`
is owned by this slug only. No other slug's PRs touch it. **No
git-merge conflict.**

### §8 Falsifiability

This STATE-SYNC is falsifiable along three axes:

1. **Bearer drift recheck (§3, §4, §5)**: if any of the 9 pin commands
   in §3.1 / §4.1 / §4.2 / §5 returns a different signature or different
   line number than this report claims, the recheck is wrong and S15
   ACT should re-pin before referencing the bearer.
2. **S12+S13 compatibility synthesis (§6)**: if any reader can identify
   a contradiction between S12's and S13's recommendations that this
   report missed (e.g. on LOC budget, Mathlib bearer choice, or
   sequencing), the synthesis is wrong and the S15 ACT plan must be
   re-evaluated.
3. **Renumbering (§6.1)**: if any subsequent ACT session uses the
   ORIGINAL S13 §7 numbering (S14 ACT = A.1) instead of this S14
   STATE-SYNC's renumber (S15 ACT = A.1), the iteration counter and
   labels get out of sync. State.md, JSON, and PR titles should all
   adopt the renumber.

### §9 Memory pattern alignment

This iteration matches:

- `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`
  — exactly: post-ship pivot to a slug whose sibling PREP merged in
  same drain wave with §X "Conflict-free guarantees" clause explicitly
  deferring state.md/JSON updates to "next STATE-SYNC iteration". This
  STATE-SYNC ships those deferred updates.
- `feedback_researcher_post_cyclerestart_pivot_synthesizes_two_sibling_preps_with_contradiction.md`
  — partially: two same-drain-wave sibling PREPs (S12 + S13) on the
  claimed slug, BUT S12 and S13 are COMPATIBLE not contradictory, so
  this S14 ships a synthesis (§6) without arbitration.

This iteration does NOT match:

- `feedback_researcher_postship_2_skip_*` patterns — the post-ship
  cycle's first claim landed on a slug with 0 open PRs and clearly
  STATE-SYNC-shaped work; no pile-up exit signal fired.
- `feedback_researcher_cyclerestart_*` patterns — wrapper fired a
  fresh session-start (PR #19322 already merged 23min ago); not a
  cycle-restart on an existing branch.

### §10 Session metrics

| Metric | Value |
|--------|-------|
| Mode | STATE-SYNC (doc-only) |
| New files | 1 (this session note) |
| Modified files | 2 (state.md, JSON) |
| Lean LOC delta | 0 |
| Sorry delta | 0 |
| Axiom delta | 0 |
| New bearer pins | 3 (`Nat.coprime_iff_isRelPrime`, `Nat.factorization_eq_zero_of_not_prime`, `isRelPrime_one_left`) |
| Pre-discharged S13 risk flags | 2 of 4 (the two unpinned-bearer flags) |
| S12+S13 contradictions surfaced | 0 |
| Effective renumber for S15+ ACTs | +1 (S14 ACT → S15 ACT, S15 ACT → S16 ACT) |

**Axiom delta this session**: 0 (documentation-only).
