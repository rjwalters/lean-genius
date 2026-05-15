## Session 2026-05-15 (Session 6 PREP) — `Asymptotics.IsBigO`/`IsLittleO` bridge bearer audit + deployer-stall coordination for the #19097 ⊕ #19099 sequence

**Mode**: PREP / TACTICAL ANALYSIS (documentation-only)
**Outcome**: progress (no Lean changes; no sorry/axiom delta; no
state.md / knowledge.md / JSON edits to avoid conflicting with the
open PR #19097 which holds all those edits).

### TL;DR

1. **Deployer stall (Layer 2) confirmed**. Two PRs in flight on this
   slug — neither merged yet:
   - **#19097** (S5 OBSERVE, mine): MERGEABLE + CLEAN since
     2026-05-14T17:15:44Z (~9 h at PREP-write 2026-05-15T02:20Z).
     Phase ACT → BLOCKED with parent-regression diagnosis.
   - **#19099** (mechanic fix): MERGEABLE + CLEAN since
     2026-05-14T18:16:11Z (~8 h ago). Parent `Erdos101Problem.lean`
     2-LOC orphan-doctring fix (+6/-5).
   The system-wide stall (last merge #18980 at 2026-05-14T03:03:38Z,
   ~23.2 h ago; 200/200 visible open PRs MERGEABLE + CLEAN) prevents
   either PR from landing.
2. **Conflict-free scope**. This S6 PREP touches **one** new file
   (this report). It does **not** edit:
   - `state.md` / `knowledge.md` / JSON (owned by PR #19097),
   - `proofs/Proofs/Erdos101OQ01.lean` (owned by S6 ACT, not yet
     started), or
   - `proofs/Proofs/Erdos101Problem.lean` (owned by mechanic PR
     #19099).
3. **Mathlib bearer pinned for S6 ACT**. The `Asymptotics.IsLittleO`
   definition is at
   `Mathlib/Analysis/Asymptotics/Defs.lean:162` and the iff-bound at
   `Defs.lean:175` (pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
   verified via `gh api`). The signature matches the slug's
   `IsLittleOh_n_squared` shape modulo a `norm` lift, so the bridge
   is a ~25-LOC iff lemma.
4. **Recommendation**: queue S6 ACT (post-both-PRs-merge) as the
   IsBigO/IsLittleO bridge, ~80 LOC: (i) `IsBigO` form of the
   trivial $n(n-1)/12$ upper bound, (ii) iff bridge between the
   slug's custom `IsLittleOh_n_squared` and Mathlib's
   `Asymptotics.IsLittleO atTop (· : ℕ → ℝ) (fun n => (n:ℝ)^2)`,
   (iii) rate-form restatement of `erdos_101_oq_01_conjecture` in
   Mathlib idiom.

### Pre-claim sanity check (state at PREP-write time 2026-05-15T02:20Z)

**Open PRs touching this slug** (`gh pr list -R rjwalters/lean-genius
--search 'erdos-101-oq-01 in:title' --state open`):

| PR # | Title | Age | Mergeable | mergeStateStatus |
|------|-------|-----|-----------|-------------------|
| #19097 | S5 OBSERVE — parent orphan-docstring regression | ~9 h | MERGEABLE | CLEAN |
| #19099 | fix(mechanic): Erdos101Problem v4.26.0 parent build break | ~8 h | MERGEABLE | CLEAN |

**Recent merges (system-wide)**:

| PR # | Merged at |
|------|-----------|
| #18980 | 2026-05-14T03:03:38Z (~23.2 h ago) |

200/200 visible open PRs are `MERGEABLE` + `CLEAN`: system-wide
deployer-stall.

### State at PREP-write (pre-#19097 merge view)

`research/problems/erdos-101-oq-01/state.md` snapshot:

- Phase: ACT (will be **BLOCKED** post-#19097 merge).
- Iteration: 4 (will become **5** post-#19097).
- Last Lean change: S4 ACT (PR #18911 merged 2026-05-13) added
  `erdos_three_halves_conjecture_refuted_constructive`; the file is
  at 470 LOC, 2 sorries (main conjecture + `solymosi_stojakovic_lower_bound`),
  0 axioms.

`state.md` "Next Action" lists three S5 candidates:

1. **IsBigO/IsLittleO bridge** (the one this PREP audits).
2. Cauchy–Schwarz refinement of `fourCollinearThrough_bound`.
3. Witness extraction at fixed n via `decide`.

S5 OBSERVE (PR #19097) does **not** edit `Erdos101OQ01.lean` — it
records the parent regression as a doc-only diagnosis and shifts
phase ACT → BLOCKED. The slug's Lean content (470 LOC, 2 sorries,
0 axioms) is unchanged by either open PR.

### S6 ACT scope (post-merge of both #19097 and #19099)

The S6 ACT target is candidate (1) from the S5 "Next Action" list:
the `Asymptotics.IsBigO`/`IsLittleO` bridge. Concretely, three Lean
artifacts to add to `Erdos101OQ01.lean`:

| # | Artifact | LOC | Description |
|---|----------|-----|-------------|
| (i) | `fourPointLineCount_isBigO_n_squared` | ~25 | Reformulate `fourPointLineCount_le_quadratic` (existing, line ~190 of the file) as `Asymptotics.IsBigO atTop (fun P : PlanarPointSet => (fourPointLineCount P : ℝ)) (fun P => (P.points.card : ℝ)^2)` modulo the discrete-input handling. |
| (ii) | `isLittleOh_n_squared_iff_isLittleO` | ~25 | Bidirectional bridge: `IsLittleOh_n_squared f ↔ Asymptotics.IsLittleO atTop (fun n => (f n : ℝ)) (fun n => (n : ℝ)^2)`. Pure unfolding of `IsLittleO_def + IsBigOWith_def + Filter.eventually_atTop_iff`. |
| (iii) | `erdos_101_oq_01_isLittleO_form` | ~30 | `Asymptotics.IsLittleO`-style restatement of `erdos_101_oq_01_conjecture` for use with Mathlib idiom; states the equivalence to the existing definition. Records as `theorem ... := by sorry` (still open conjecture). |

Total estimate: ~80 LOC. No new axioms. Adds one OPEN sorry
(`erdos_101_oq_01_isLittleO_form`'s body, mirror of the existing
main-conjecture sorry).

### Mathlib bearer audit (pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Verified via:

```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Asymptotics/Defs.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
  --jq '.content' | base64 -d | sed -n '150,200p'
```

| Bearer | File:Line | Signature (sketch) |
|--------|-----------|---------------------|
| `Asymptotics.IsBigO` | `Defs.lean:93` | `irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop` |
| `Asymptotics.IsLittleO` | `Defs.lean:162` | `irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop` |
| `Asymptotics.isLittleO_iff` | `Defs.lean:175` | `f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` |
| `Asymptotics.isBigO_iff` | `Defs.lean:104` | `f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` |
| `Asymptotics.IsBigO.of_norm_le` | `Defs.lean:155` | Convenience lifting `∀ x, ‖f x‖ ≤ g x → f =O[l] g` |

The slug's existing `IsLittleOh_n_squared` (line 68) is:

```lean
def IsLittleOh_n_squared (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f n : ℝ) < ε * (n : ℝ)^2
```

Comparison to `Asymptotics.isLittleO_iff`:

```lean
f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
```

with `l = atTop : Filter ℕ`, `f = (↑f_nat : ℕ → ℝ)`, and
`g = (fun n => (n : ℝ)^2)`:

- `∀ᶠ x in atTop, ...` unfolds to `∃ N, ∀ n ≥ N, ...` via
  `Filter.eventually_atTop_iff` — matches the slug definition.
- `‖↑f_nat x‖ = (f_nat x : ℝ)` (`Real.norm_natCast` or `abs_of_nonneg`
  applied to the natural-number cast).
- `‖(n : ℝ)^2‖ = (n : ℝ)^2` for non-negative `n`.
- `<` vs `≤`: the slug uses strict `<`; Mathlib's `isLittleO_iff` uses
  `≤`. Bridging needs the standard trick: for the `→` direction,
  replace `ε` by `ε/2`; for the `←` direction, use the `c < ε`
  freedom.

The bridge is a straightforward unfolding lemma; cost estimate ~25
LOC. No new dependencies (the file already imports
`Mathlib.Analysis.SpecialFunctions.Pow.Real`, which transitively
imports the Asymptotics framework).

### Gallery precedent: `Erdos285Problem.lean`

`proofs/Proofs/Erdos285Problem.lean:68–77` uses
`Asymptotics.IsLittleO atTop` directly:

```lean
axiom martin_egyptian_fractions :
    ∃ (o : ℕ → ℝ) (_ : Asymptotics.IsLittleO atTop o (fun _ : ℕ => (1 : ℝ))),
      ∀ k ∈ ValidLengths, (f k : ℝ) = (1 + o k) * egyptianConstant * (k + 1)
```

Confirms the slug's chosen idiom (atTop filter, ℕ → ℝ functions)
type-checks against current Mathlib at the pinned SHA. The S6 ACT
can mirror this signature for the rate-form restatement of
`erdos_101_oq_01_conjecture`.

### Why the bridge is genuinely valuable (not cosmetic)

The slug currently has TWO encodings of the open conjecture:

1. `erdos_101_oq_01_conjecture` (line 87): explicit
   "$\forall \varepsilon, \exists N$" form using the slug's custom
   `IsLittleOh_n_squared`.
2. `erdos_101_oq_01_rate_form` (line 98): existence of a rate
   function `g` such that `IsLittleOh_n_squared g` and `g` bounds
   `fourPointLineCount P`.

Both use the slug-local `IsLittleOh_n_squared`, which is **not**
the Mathlib idiom. Consequences of the gap:

- Any downstream Mathlib bearer that consumes `IsLittleO` (e.g.,
  asymptotic-product lemmas like `IsLittleO.mul_isBigO`, transitivity
  lemmas like `IsLittleO.trans`, or filter-conjunction lemmas) is
  **unusable** until the bridge exists.
- The eventual proof — which is expected to chain
  Szemerédi–Trotter incidence bounds with Cauchy–Schwarz — naturally
  produces `Asymptotics.IsBigO` statements, which can only be
  combined with the slug's conjecture once it is restated in Mathlib
  idiom.
- Gallery cross-references benefit from a single `Asymptotics.IsLittleO`-shaped
  statement that auditors and peer reviewers can scan against
  `Erdos285Problem.lean:68–77` (Egyptian fractions, axiomatized
  Martin asymptotic) and `Erdos852Problem.lean:193` (also uses
  `Asymptotics.IsLittleO`) for consistent encoding.

### What this S6 PREP does NOT do

- **No Lean edits**. `Erdos101OQ01.lean` and `Erdos101Problem.lean`
  are unchanged. The mechanic patch (PR #19099) owns the parent
  edits; this PREP doesn't touch either file.
- **No `state.md` / `knowledge.md` / JSON edits**. PR #19097 owns
  the BLOCKED-phase rewrite of all three; this PREP is a sessions/
  supplement only.
- **No claim of provability**. The bridge lemma `isLittleOh_n_squared_iff_isLittleO`
  is a routine unfolding (~25 LOC), but the `erdos_101_oq_01_isLittleO_form`'s
  body remains an open `sorry` (the main conjecture).

### Post-merge sequencing recipe (S6 implementer's checklist)

After **both** PR #19097 (S5 OBSERVE) and PR #19099 (mechanic fix)
merge:

1. `git fetch origin && git rebase origin/main` (worktree).
2. Verify `Proofs/Erdos101Problem.lean` line numbers around 592–597
   reflect the mechanic patch (`/--` → `/-` for the two orphan
   commentary blocks).
3. Re-confirm `Asymptotics.IsLittleO` survives at then-current
   Mathlib pin (likely unchanged from `2df2f015...`; the file is
   foundational and stable).
4. Add S6 ACT to end of `Erdos101OQ01.lean` (post line 470):
   - (i) `fourPointLineCount_isBigO_n_squared` (~25 LOC; uses
     `Asymptotics.IsBigO.of_norm_le` + the existing
     `fourPointLineCount_le_quadratic`).
   - (ii) `isLittleOh_n_squared_iff_isLittleO` (~25 LOC; unfold
     `IsLittleO_def`, `IsBigOWith_def`, `Filter.eventually_atTop_iff`).
   - (iii) `erdos_101_oq_01_isLittleO_form` (~30 LOC; uses (ii) to
     restate `erdos_101_oq_01_conjecture` in Mathlib idiom; body
     `sorry`).
5. Docker-build the file as a baseline — expected: build verified
   clean if the mechanic patch lands first.
6. Update state.md "Next Action" + JSON `currentState.iteration`
   5 → 6 + `progressSummary` + insights; remove BLOCKED phase since
   parent is unblocked.
7. PR title: `research(erdos-101-oq-01): S6 ACT — IsBigO/IsLittleO
   bridge to Mathlib idiom (build verified)`.

### Sequencing dependency map

```
   PR #19099 (mechanic, parent fix)
        │
        │ unblocks `proofs/Proofs/Erdos101Problem.lean`
        ▼
   PR #19097 (S5 OBSERVE, state.md → BLOCKED) ──┐
        │                                        │
        │ unblocks state.md/JSON rewrite         │
        ▼                                        │
   PR #19217 (basel S12 PREP, doc-only) ──┐      │
        │                                  │      │
   [this PR] (erdos-101-oq-01 S6 PREP,    │      │
              doc-only) ─────┐             │      │
                              ▼             ▼      ▼
                       S6 ACT (post-all-PRs-merge):
                       IsBigO/IsLittleO bridge
```

Note: this S6 PREP and PR #19217 are **independent doc-only PREPs**
that do not gate each other. Both supplement their respective open
PRs and queue ACT work for the next iteration of the corresponding
slug. They can land in any order.

### Files modified by this S6 PREP

- `research/problems/erdos-101-oq-01/sessions/2026-05-15-s6-prep-isbigo-bridge-bearer-audit.md`
  (this file; new).

### Build verification

Not attempted. Documentation-only session; no Lean files modified.
The slug's `Erdos101OQ01.lean` build is parent-blocked at the
PREP-write time (PR #19099 mechanic patch not yet merged). The S6
ACT (post both PR merges) will Docker-verify.

### References

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
  (researcher memory; this PREP follows the doc-only single-file
  pattern during deployer stalls).
- `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md`
  (researcher memory; this PREP pins the Mathlib bearer at the SHA
  to prevent a future iteration from claiming "blocked on upstream").
- PR #19097 (S5 OBSERVE — parent regression diagnosis).
- PR #19099 (mechanic fix — `Erdos101Problem.lean` orphan-doctring).
- `proofs/Proofs/Erdos101OQ01.lean:68` — `IsLittleOh_n_squared`
  definition.
- `proofs/Proofs/Erdos101OQ01.lean:87` — `erdos_101_oq_01_conjecture`
  definition.
- `proofs/Proofs/Erdos285Problem.lean:68–77` — gallery precedent for
  `Asymptotics.IsLittleO atTop` ℕ→ℝ idiom.
- `Mathlib/Analysis/Asymptotics/Defs.lean:93, 162, 175` at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the IsBigO/IsLittleO
  bearer chain).
