# Operator-directed revision (`--polish "<reason>"`) snippet

Canonical convention for the **operator-directed revision** flag —
the sanctioned, audit-trailed path for spending one additional
revision pass when the combined-verdict pre-check would otherwise
force a terminal exit (issue #691). This is the single source of truth
referenced by each skill's SKILL.md and `*-revise.md` command file; a
command file's `--polish` step is a pointer to this snippet, exactly
like the `_progress.json` convention points at `progress.md` and the
per-phase commit hook points at `git_sync.md`.

The flag is named **`--polish`**, reusing the `memo` skill's existing,
merged contract (issue #201) rather than inventing a second
vocabulary. `--polish` and the issue's originally-proposed `--directed`
describe the same operator action — spend a sanctioned extra iteration
when the critics already passed — and shipping both would fragment the
vocabulary. This snippet generalizes memo's contract so every
report-family reviser can adopt it with a one-line name/threshold
delta.

## Why this exists

Passing the rubric threshold and having nothing worth fixing are
**different states**, but the combined-verdict pre-check in every
`*-revise` command conflates them: when the review records
`advance: true` and (where an audit critic exists) the audit is clean,
the command reports the terminal state and exits WITHOUT writing. The
framework's convergence semantics are correct — thresholds decide
*advance*, not *perfection* — but they leave no legitimate path for an
operator to spend one more iteration on concrete, enumerated minors
that the critics' own output already listed.

The canary friction (Botho #881, the `primer` run in issue #691):
a version passed (41/44 + clean audit) yet the critic sidecars listed
an order-of-magnitude gap, jargon-before-teaching spots, a
non-reproducible headline number, and a fee formula missing a term.
For public-facing collateral, shipping those is worse than one more
iteration. The operator waived the pre-check by prompt-level override
("OPERATOR OVERRIDE of step N: …") — which *works* (each override
produced a strictly better artifact, re-scored on its own merits by a
fresh critic pair, within the iteration cap) but exists **outside the
documented contract**: a conservative reviser agent could reasonably
refuse it, and nothing pins down what a legitimate waiver must
preserve. `--polish` makes the override a first-class, documented path.

## The flag: `--polish "<reason>"`

A CLI flag on the `*-revise` command. When passed, the reviser
bypasses the combined-verdict pre-check step, allowing the reviser to
run against an already-passing version (which the default path
correctly refuses). The polish pass targets the line-level signal the
default "fix what's broken" path skips:

1. **Sub-threshold per-dimension justifications** in the review's
   `scoring.md` — any dimension where the critic flagged room to grow
   (e.g., "5/6 — clear but the conditional terms could be sharper").
2. **`comments.md` line-level notes** tagged `nit` or untagged — i.e.,
   suggestions that did not rise to `blocker` / `major`.
3. Any optional audit / secondary critic siblings, on the same terms
   as a normal revise pass.

### Required, non-empty reason (load-bearing)

The reason argument is **required**. `--polish` with no value,
`--polish ""`, and `--polish "   "` (whitespace-only) are all rejected
with a clear error pointing at this rule, and the thread is left
**untouched** (no version dir written, no `_progress.json` mutation).
This mirrors the deck skill's `iteration_cap_rationale` rejection
pattern — an unjustified override is treated as malformed. Operators
MUST supply substantive intent (e.g., *"Sharpen the demurrage
order-of-magnitude figure and the fee formula's missing term flagged
in the audit sidecar; land the four jargon-before-teaching fixes from
the review comments."*).

The reason lives on disk as the audit trail (see §"Audit-trail
fields") and is quoted verbatim in the revision's `changelog.md`
header note.

### What `--polish` bypasses (scope of the waiver)

**The combined-verdict pre-check step ONLY.** Every other guard still
fires:

- **The iteration-cap check still applies.** A polish pass against a
  thread already at `max_iterations` still hits the `BLOCKED` notice —
  the operator cannot use `--polish` to escape the cap.
- **The critic-completeness check still applies.** The reviser still
  requires the same critic siblings the default path requires (for the
  report-family shape: BOTH a completed review AND a completed audit).
  Running `--polish` without a fresh review/audit pair is rejected in
  the same shape as the default path's "no critic to revise against"
  error. `--polish` bypasses the *verdict* of the pre-check, never the
  *existence* of the critics.
- **Critical-flag handling is unchanged.** By definition a
  polish-eligible version has zero unresolved critical flags (that is
  what the pre-check verified). `--polish` does not, and cannot, be
  used to skip a critical flag.

### No inherited credit (load-bearing)

The polish-pass output is a **normal** `<thread>.{N+1}/` version dir,
immutable, following the reviser contract. It gets **NO inherited
credit** from the version it revised:

- The next critic pass scores `<thread>.{N+1}/` on **its own rubric
  merits**. A fresh critic pair MUST land for the thread to
  re-reach the terminal state — the state machine already enforces
  this; `--polish` does not shortcut it.
- The reviewer/auditor at the next pass does **NOT** read the
  audit-trail fields, does NOT special-case the polish pass, and does
  NOT apply a "be lenient because the operator forced this" path. The
  fields are operator-side disclosure only.
- `--polish` is **single-pass**: it produces exactly one
  `<thread>.{N+1}/`, never loops, never consults a target score, never
  re-invokes itself.

### Changelog discipline

The polish pass's `changelog.md` obeys the same mapping discipline as
any revise pass: each change maps to a specific critic note (a
sub-threshold dimension deduction, a `nit`/untagged comment, an audit
finding) **or** to the operator directive quoted verbatim in the
`--polish` reason. A polish pass that changes body text without a
traceable source is a defect. The prior review's do-not-sand-off
list — the critics' "What's working" / flagged-as-load-bearing
moves — **binds**: rubric-point chasing that flattens a
flagged-as-working move is the named meta-failure mode, and `--polish`
does not license it.

### Audit-trail fields

The polish-pass version dir carries two `metadata` extensions in its
`_progress.json` as the on-disk audit trail (per the shallow-merge
recipe in `progress.md` — any subsequent command that touches
`_progress.json` preserves them):

- `metadata.revision_mode = "polish"` (default path: `"normal"`, or
  the field is absent — readers tolerate both).
- `metadata.revise_force_reason = "<verbatim operator-supplied
  reason>"` (default path: `null` or absent). Stored **verbatim** — no
  trimming, no normalization, no truncation beyond what JSON encoding
  requires.

**State-machine impact: none.** Both fields are audit-trail-only —
NOT scored, NOT gating, NO state-machine impact. A version dir with no
`--polish` is byte-identical to the pre-adoption shape.

## Default (no-flag) behavior is byte-identical

The `--polish` path is **purely additive**, gated entirely behind the
flag. When `--polish` is absent, the `*-revise` command's numbered
procedure is unchanged: the combined-verdict pre-check that would exit
with the terminal report still exits with the terminal report, writing
nothing. Absent-flag == today's behavior. Adoption adds a
flag-gated branch to the pre-check step; it changes no other step's
meaning.

## Which commands adopt

Every `*-revise` command has *some* combined-verdict pre-check step
that exits/reports terminal without writing when the critics already
passed. The full set (12 skills): `memo`, `report`, `datasheet`,
`proposal`, `primer`, `deck`, `paper`, `slides`, `installation`,
`essay`, `ip-uspto`, `ip-uspto-provisional`.

**Rollout is phased** (issue #691). Adopted so far:

- **`memo`** — the original consumer (issue #201). `memo-revise`
  composes `--polish` with a `--scope` severity filter and a
  `--plan`/`--apply` preview mode; those compositions are
  memo-specific and stay documented in `memo-revise.md`.
- **`primer`** — the second consumer and this snippet's origin (issue
  #691). Bypasses the step-2 combined-verdict pre-check; the
  report-family review+audit critic-completeness check (step 1) and
  the iteration cap (step 3) still apply.
- **`proposal`** — the third consumer (issue #862). Bypasses the
  step-4 combined-advance pre-check; the review+audit
  critic-completeness check (step 1) and the iteration cap (step 3)
  still apply. Composes with proposal's existing `--scope` severity
  filter on the same terms `memo-revise.md` documents (the polish
  bypass and the scope filter are independent, orthogonal flags).

**Pending adoption** (each its own scoped follow-up PR, referencing
this snippet): `report`, `datasheet`, `deck`, `paper`, `slides`,
`installation`, `essay`, `ip-uspto`, `ip-uspto-provisional`. The
`essay` and `installation` shapes are review-only (no audit), so their
bypass is even simpler — skip the single-critic verdict pre-check
step.

## Adoption step (the prose to put in a command file)

A `*-revise` command file adopts the contract with a `## CLI flags`
section containing a `### --polish "<reason>"` subsection that:

1. Points at this snippet as the source of truth for the generic
   contract.
2. Names the **specific numbered pre-check step** the flag bypasses in
   that command (e.g., "step 2" for `primer`, "step 4" for `report`).
3. Restates the per-skill guards that STILL apply (the
   critic-completeness step and the iteration-cap step, named by their
   local step numbers), so a reader sees the exact scope of the waiver
   without cross-referencing.
4. Adds a `--polish` bypass note at the pre-check step itself, so the
   procedural body carries the branch inline.

The SKILL.md adopts a short §"Operator-initiated polish passes"
cross-reference pointing at this snippet for the full contract (rather
than re-deriving it), mirroring `memo/SKILL.md`.

## See also

- `progress.md` — the `_progress.json` `metadata` shallow-merge recipe
  the audit-trail fields participate in.
- `git_sync.md` — the sibling opt-in-behavior snippet this file is
  modeled on (generic contract + per-skill deltas + adoption prose).
- `anvil/skills/memo/commands/memo-revise.md` §"CLI flags" — the
  original `--polish` implementation, plus the memo-specific `--scope`
  / `--plan` / `--apply` compositions.
- `anvil/skills/primer/commands/primer-revise.md` §"CLI flags" — the
  report-family (review+audit) adoption.
- `anvil/skills/proposal/commands/proposal-revise.md` §"CLI flags" —
  the review+audit adoption that also composes with an existing
  `--scope` severity filter.
