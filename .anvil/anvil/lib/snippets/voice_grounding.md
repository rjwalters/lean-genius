# Voice grounding: persona docs as drafting and review substrate

This snippet codifies the **voice/persona grounding-docs contract**
(issue #461) — how a project declares the voice artifacts that define
its author persona, how drafters ground new prose in them, and how
reviewers calibrate voice-fidelity judgment against them. The contract
generalizes the proven shape from the rjwalters.info blog pipeline
(`STYLE_GUIDE.md` / `VOCABULARY.md` / `VALUES.md` / published-post
corpus + `blog-review.md`), where every draft/review/revise pass is
grounded in four voice artifacts.

This is the **judgment-side** contract. Deterministic vocabulary
screening — AI-tell word counting, banned-phrase matching, em-dash
frequency analysis — belongs to the rhetoric lint (issue #463), NOT
here. A reviewer following this snippet MAY note vocabulary tells in
prose, but builds no counting machinery; the lint is the mechanical
pre-flight, this contract is the calibrated judgment that runs after
it.

## The four-doc taxonomy

A project declares up to four voice artifacts via ONE optional
top-level key in the project `BRIEF.md` frontmatter (parsed by
`anvil/lib/project_brief.py::VoiceDocs`):

```yaml
voice:
  style_guide: .anvil/voice/STYLE_GUIDE.md   # optional — register / cadence rules
  vocabulary: .anvil/voice/VOCABULARY.md     # optional — AI-tell guidance (judgment side only)
  values: .anvil/voice/VALUES.md             # optional — stances / anti-stances / standing /
                                     #            voice signatures / failure modes
  corpus: writing-corpus/**/*.md     # optional glob — published exemplars quoted
                                     #                 as voice ground truth
  rhetoric_rules: rhetoric-rules.json  # optional — consumer JSON rules for the
                                       #            rhetoric lint (gate side; NOT
                                       #            a grounding doc — see below)
```

| Doc | Role | What it carries |
|-----|------|-----------------|
| **values** | Who the author is | Stances and anti-stances, standing (what the author has earned the right to say), voice signatures, named failure modes |
| **style_guide** | How the author sounds | Register, cadence, sentence-shape rules, structural habits |
| **vocabulary** | What the author would never say | AI-tell word guidance ("delve", "tapestry", …), frequency discipline notes |
| **corpus** | Proof | Published exemplars — the ground truth a reviewer quotes when judging whether new prose sounds like the author |

Every sub-key is optional; the block itself is optional.

**Starter templates ship for all three authored doc kinds** (issues
#576, #578): `anvil/templates/voice/STYLE_GUIDE.template.md`,
`anvil/templates/voice/VOCABULARY.template.md`, and
`anvil/templates/voice/VALUES.template.md` are generalized,
de-personalized starting points (schema, not content — every
author-specific example, stance, anti-stance, and standing claim is a
marked `<!-- replace me -->` placeholder; no real author beliefs ship).
A consumer adopting voice grounding does not start from a blank page:
`scripts/install-anvil.sh` scaffolds them under `.anvil/voice/` as
`.anvil/voice/STYLE_GUIDE.md` / `.anvil/voice/VOCABULARY.md` /
`.anvil/voice/VALUES.local.md` (per-file skip-if-exists, never clobbering
an existing grounding doc — a pre-#617 root-level copy is also preserved
and suppresses the new scaffold) when a voice-consuming skill (`essay` /
`memo`) is selected. The docs resolve against the consumer root, so a
declared `.anvil/voice/STYLE_GUIDE.md` loads exactly as the older
root-level path did. **`VALUES.md` is
private by default** (issue #578): it carries first-person stances /
anti-stances / standing, so it scaffolds to a gitignored
`VALUES.local.md` (the `*.local.md` path #577 ships) rather than a
committed `VALUES.md` — a gitignored declared doc resolves and grounds
identically to a committed one (see "## Private grounding" below). See
`anvil/templates/voice/README.md`. The optional **vocab reminder tool**
(issue #579) ships at `anvil/lib/vocab_reminder.py` (`python -m
anvil.lib.vocab_reminder [count]`) — the generative-reminder complement
to the judgment-side `VOCABULARY.md`. It is a *reminder, not an
injector*: it surfaces precision-word candidates for a human to consider,
never auto-applies them, and the drafter MUST NOT mechanically substitute
sampled words (see the essay drafter's step-3 reminder note). It draws
from a sibling `*.words.txt` next to the declared `voice.vocabulary` doc
when present, else a small anvil default.

**`rhetoric_rules` is the asymmetric fifth sub-key** (issue #468): a
path to a consumer **JSON rule file** consumed by the render gate's
advisory `memo_rhetoric_lint` check (issue #463) — lint-side
configuration, NOT a grounding doc. It never enters the drafter's load
order or the reviewer's calibration, is excluded from
`resolve_voice_docs` output, and does NOT count toward
`VoiceDocs.is_empty`: a `rhetoric_rules`-only `voice:` block activates
only the lint wiring (resolved by
`anvil/lib/project_brief.py::resolve_rhetoric_rules`, same
project-root-then-consumer-root walk) and never the judgment tier
below. A declared-but-missing rule file is still forwarded to the gate,
where the lint emits one warning finding naming the error and runs
defaults-only (the same defect-to-surface posture as the grounding
docs, with zero extra machinery).

**Voice-sample precedence: when the resolved corpus contradicts a
default lint rule, override the rule — not the corpus.** A project's
`corpus` exemplars sometimes show a real authorial habit (the em-dash
case is canonical) at a frequency the rhetoric lint's generic
AI-tell defaults would flag. The documented fix lives on the lint side,
not here: declare a project-local `voice.rhetoric_rules` file that
`disable`s the specific default rule id(s) (e.g. `em-dash-density`,
`no-opening-emdash`) rather than loosening the framework default for
every project. See `anvil/lib/rhetoric_lint.py`'s module docstring,
section "Voice-sample precedence (a per-project override, not a
framework default change)", for the full worked example. A drafter or
reviewer who has already loaded the `corpus` for judgment-side
calibration is looking at exactly the evidence needed to decide whether
this override applies.

## Activation pattern (the #428/#452 contract)

- **No `voice:` block → byte-identical behavior.** No suffix, no
  `_summary.md` block, no `_progress.json` field, no extra reads.
  Consumers that never declare the block never see this contract.
- **Declared-but-missing file → the tier ACTIVATES** and the breakage
  surfaces as a **`major` review finding** directing the operator to
  create or fix the file. A broken declaration is a defect to surface,
  not an opt-out and not a crash (the
  `anvil/skills/report/lib/customer_context.py` posture).
  `resolve_voice_docs` carries missing files as structured
  `missing: true` entries; it never raises on absence.
- **Empty block (`voice: {}`), unknown-sub-keys-only block, or
  `rhetoric_rules`-only block → inactive** for this judgment tier,
  same as absent (`VoiceDocs.is_empty`; the `rhetoric_rules` sub-key
  is recognized but gate-side — it activates only the rhetoric-lint
  wiring, see above). Unknown sub-keys are preserved verbatim under
  `unknown_keys` with a warning (forward-compat).

## Path resolution: project root first, then consumer root

Relative declared paths resolve against the **project root first, then
the consumer root** (the directory carrying the `.anvil/` install
marker, located via `anvil/lib/theme.py::find_consumer_root` — the
#322/#394 walk; first hit wins). Voice docs are usually persona-level
repo-root artifacts shared across every project in the consumer repo,
but a project ghostwriting in a different persona can shadow them
locally. The `corpus` value is a glob (`**` supported); a root "hits"
when the glob matches at least one file; matches are sorted. Use
`anvil/lib/project_brief.py::resolve_voice_docs(project_dir,
consumer_root=None)` — do not re-implement the walk.

## Private grounding (`.gitignored` personal docs)

The personal layer of voice grounding — *what the author believes,
what they refuse to say, what they have standing to claim*
(`VALUES.md`-class content) — is exactly the material many consumers
will NOT want committed into a shared or public repo. Anvil makes
**private grounding a designed, tested, protected posture** so those
consumers neither commit personal stances publicly nor skip the
highest-leverage grounding doc.

This works because resolution is **filesystem-driven and never
consults git status**: `resolve_voice_docs` walks project-root then
consumer-root and resolves a declared doc whether or not it is tracked
by git. A `.gitignored` declared doc resolves and activates the tier
**identically to a committed one** — same load order, same drafter
grounding, same reviewer calibration, same `major` finding when it is
declared-but-missing. There is no separate "private" code path and no
special-casing; privacy is a property of where the file lives in git,
not of how anvil reads it.

### The convention

- **Default (documented): the `*.local.md` suffix.** Name a private
  grounding doc with a `.local.md` suffix (e.g. `VALUES.local.md`) and
  declare it in the `voice:` block like any other doc. The suffix has
  industry precedent (dotenv `.env.local`, Vite `*.local`) and reads
  unambiguously as "private overlay, do not commit." The scaffolder
  gitignores `*.local.md` with a single pattern line.
- **Supported alternative: a `.voice/` locus.** A consumer who prefers
  a directory boundary may keep private docs under a gitignored
  `.voice/` directory (e.g. `.voice/VALUES.md`) and declare that path.
  One `.gitignore` line (`/.voice/`) covers the whole locus. This is
  supported but not the documented default — pick one convention per
  repo and stay consistent.

Either way the declaration is ordinary `voice:` grammar — there is no
new config surface and no `--private` flag in the BRIEF:

```yaml
voice:
  style_guide: STYLE_GUIDE.md      # committed — team-shared register
  values: VALUES.local.md          # private  — gitignored personal stances
```

### What "private" guarantees

- The doc **resolves and grounds** drafting and review identically to
  a committed doc (the filesystem-driven resolver above).
- The scaffolder **appends its path to `.gitignore`** idempotently
  (see `scripts/install-anvil.sh` Stage 7.9 and
  `anvil/templates/voice/README.md`).
- **Anvil's own git-sync hook will never stage or commit it** (the
  opt-in per-phase commit hook, `anvil/lib/snippets/git_sync.md`; the
  guard is stated there under §"Staging scope").

### What "private" does NOT guarantee

State this plainly so operators do not over-trust the model:

- It is **not encryption.** The file sits in plaintext on disk; anyone
  with filesystem access reads it.
- It is **not protection against a human or a non-anvil tool.** A
  `git add -f <path>` force-adds a gitignored file, and any other tool
  that runs `git add -A`/`-f` can stage it. Anvil's guarantee is only
  about *anvil's own* git activity (the git-sync hook), which never
  uses `-f` and never `git add -A`.
- It **does not stop the doc's *influence* from appearing in committed
  prose.** That is the point: the voice is grounded by the private
  stances, but only the resulting artifact is committed — the source
  document stays private, its effect does not.

### Intended user

`VALUES.md`-class personal stances are the intended user of private
grounding (the canonical `VALUES.local.md`): stances and anti-stances,
standing, voice signatures, named failure modes — the content authored
in the first person that an author would not publish verbatim. The
`VALUES.md` schema + starter template is tracked by issue #578, which
is a **downstream consumer** of this private path: it simply declares a
`VALUES.local.md` (or `.voice/VALUES.md`) using the mechanism shipped
here.

### Layering (committed base + private overlay): DEFERRED

A committed team-level base supplemented by a private personal overlay
(e.g. `VALUES.md` committed + `VALUES.local.md` gitignored, merged or
last-wins) is **deliberately deferred** to a follow-up (epic #575).
Anvil ships the **single-private-doc model first**. Rationale:

1. Merge/last-wins semantics multiply the resolver's surface —
   `resolve_voice_docs` returns one `ResolvedVoiceDoc` per declared
   kind today; layering would require a list-per-kind or a merge step,
   touching every downstream consumer of `ResolvedVoiceDoc`.
2. The single-private-doc model already solves the stated need (a
   private `VALUES.md`).
3. The `*.local.md` suffix convention chosen above leaves the door
   open to add layering later without a breaking change (the overlay
   already has a name).

If layering is later shipped it must define merge semantics precisely
and update the four-doc load-order docs above.

## Drafter contract

When the voice tier is active, the drafter:

1. **Loads the declared docs in order: values → style_guide →
   vocabulary → corpus exemplars.** Values first — the stances and
   standing constrain what may be said before register shapes how it
   is said.
2. **Chooses 3–5 corpus exemplars** that are **voice-matched AND
   topically adjacent** to the artifact being drafted. Not the whole
   corpus — a handful of exemplars read closely beats fifty skimmed.
3. **Records the consulted exemplar paths in `_progress.json`** under
   `metadata.voice_exemplars` (a list of path strings) so the reviewer
   can check that grounding actually happened. No `voice:` block → the
   field is omitted entirely.
4. **Quotes a corpus passage when justifying a register or mode
   choice** in its self-check — the same evidence discipline the
   reviewer is held to below.

Missing declared docs do not block drafting: the drafter proceeds with
whatever resolved, and the reviewer surfaces the broken declaration.

## Reviewer contract

When the voice tier is active, the reviewing skill calibrates its
**owned dimension** (the skill names which one — memo uses dim 8
*Prose & structure*; see `anvil/skills/memo/rubric.md` §"Dim 8 —
voice-grounding calibration") against the resolved voice docs, via the
skill's triggered-suffix mechanism (the #348 composition-order
precedent). Rules:

- **Every voice deduction MUST quote a corpus passage** showing what
  the target voice sounds like. Vague feedback ("this doesn't sound
  like you") is insufficient — the deduction names the offending
  artifact passage AND quotes the exemplar passage it falls short of.
  This is the load-bearing discipline that makes the consumer's loop
  work; a voice deduction without a corpus quote is itself a defective
  finding. (Complementary, not conflicting, with the quoted-evidence
  sub-rule in `rubric.md` §"Dimension scoring guidance" rule 1, which
  quotes the *reviewed body* — a voice deduction under both contracts
  quotes BOTH the offending body passage and the corpus exemplar, as
  this rule already requires.)
- **The convergence-with-Claude adversarial check**: for each passage
  under voice scrutiny, the reviewer asks — *would I, the AI, also
  write this sentence?* If yes, scrutinize harder, never defend.
  Convergence between the artifact's voice and the reviewing model's
  own default register is the biggest meta-failure mode of AI-assisted
  voice work: the reviewer's instinct to approve prose it would have
  produced itself is precisely the signal that the persona has been
  flattened.
- **Anti-stance violations are critical-flag candidates.** When the
  values doc declares anti-stances, substrate, or standing limits, a
  violation routes through the skill's **existing** critical-issue
  machinery (the memo `hard_rules` precedent) — not a new flag
  category. The flag justification quotes the violated values-doc
  passage.
- **Vocabulary tells are noted, not counted.** The reviewer may cite
  vocabulary-doc guidance in prose findings, but deterministic
  screening (word counts, em-dash frequency) is the rhetoric lint's
  job (issue #463).

## `_summary.md` block

When the tier is active, the reviewer's `_summary.md` carries a
top-level `voice_grounding` block:

```json
"voice_grounding": {
  "ran": true,
  "docs_loaded": ["/abs/path/VALUES.md", "/abs/path/STYLE_GUIDE.md"],
  "exemplars_quoted": 2
}
```

`docs_loaded` lists the resolved paths actually read (load order);
`exemplars_quoted` counts the corpus passages quoted across the voice
findings. When declared docs were missing, add a `"missing":
["<declared path>", …]` list naming them (the `major` finding carries
the remediation).

**When the tier is inactive (no `voice:` block in the project BRIEF),
the block is NOT emitted at all** — no `{ran: false}` entry. This
deliberately matches the customer-context activation convention
(absent declaration = absent block = byte-identical output), NOT the
`ran: false` explicit-skip convention used for substrate-driven
sub-steps like `summary_detail_consistency`. The difference: those
sub-steps are always-on framework behavior whose skip needs
explaining; this tier simply does not exist for projects that never
declared it.

## Self-published exclusion (issue #890)

A `voice.corpus` glob is naturally the consumer's own published archive
(the ground truth for "does this sound like the author"). That is
correct when drafting a **new** thread, and **circular** when
reviewing a **revision of an already-published one** — the thread's
own prior published form sits inside its own calibration base, so a
reviewer scoring dim-2-class deductions against it is partly grading
the artifact against itself. `essay-review` is the shipped consumer of
the fix (`anvil/skills/essay/commands/essay-review.md` step 4); any
other reviewing skill in the same "revision of a previously-published
thread" shape can adopt it identically.

`resolve_voice_docs(project_dir, consumer_root=None, *,
exclude_self_slug=None)` (issue #890) takes an optional keyword-only
`exclude_self_slug`. When supplied with the slug of the thread
currently under review, the resolved `corpus` entry has that thread's
own published form dropped from `paths` before it reaches the reviewer
— two exclusion sources, unioned and deduped:

1. **Automatic inference.** A resolved corpus path whose filename
   stem, after optionally stripping one leading `YYYY-MM-DD-` date
   prefix, case-insensitively **equals** `exclude_self_slug` exactly.
   Deliberately narrow (no substring/prefix/suffix matching) — a false
   positive would silently exclude an unrelated thread's legitimate
   exemplar with no operator-visible signal, which is worse than the
   false negative the declared escape hatch below exists to close.
2. **Declared `voice_corpus_exclude`** — an optional per-document field
   on the matching `documents:` entry (`BriefDocument.voice_corpus_exclude`),
   same scalar-or-list path/glob shape as `spec_ref` / `code_ref`,
   resolved the same way (project-root first, then consumer-root):

   ```yaml
   documents:
     - slug: the-loop-is-the-unit
       artifact_type: essay
       voice_corpus_exclude: writing-corpus/the-loop-is-the-unit-reprint.md
   ```

   This is the documented escape hatch for a publish-path convention
   the automatic rule cannot infer (a title-cased filename, a
   transliterated slug, a nested `index.md`-per-post layout). A pattern
   that resolves to nothing is a silent no-op — this field only ever
   *narrows* an already-resolved corpus, never widens or breaks it.

`exclude_self_slug=None` (the default) is a **complete no-op** —
every pre-#890 caller of `resolve_voice_docs` (memo, report, memoir,
essay-draft) sees byte-identical output whether or not it upgrades.

**Auditability.** A dropped path is never silent: the resolved
`ResolvedVoiceDoc` carries `excluded` (the sorted list of dropped
absolute paths) and `exclusion_reasons` (a `{path: reason}` map, e.g.
`"published self (inferred from slug)"` or `"declared corpus_exclude:
'<pattern>'"`). A reviewing skill's `_summary.md.voice_grounding` block
should surface this as `corpus_excluded: [{path, reason}, …]` — see
`anvil/skills/essay/commands/essay-review.md` step 9 for the shipped
shape.

**Thin-corpus guard.** Excluding the self-published form can leave very
few (or zero) independent exemplars — a two-note corpus with one
excluded leaves a single exemplar, which one reviewer in the session
that motivated this issue noted post-dated the artifact under review by
three days. `resolve_voice_docs` does not itself impose a minimum —
that judgment call belongs to the consuming skill's review command
(essay-review's documented threshold is **2**: fewer remaining paths
after exclusion triggers a `corpus_thin: true` note rather than a
silent full-confidence calibration).

## Reviser contract (one line)

When the tier is active, the reviser reads the resolved voice docs
alongside the critic feedback and **preserves voice signatures the
reviewer flagged as working** — voice-grounded revision must not
sand off the persona while chasing rubric points.

## Subject voice tier (issue #598)

Everything above grounds the **author persona** — "does new prose sound
like the author?" The **subject voice tier** points the same machinery
at a *third party whose dialogue is rendered in the artifact*: a
memoir reconstructing a grandmother's speech from interview
transcripts, a `report` engagement narrative quoting a customer, a
`paper` quoting a study participant, an oral-history project. The ground
truth is a **spoken corpus** (recorded speech), not published prose,
and the question is "does this reconstructed line sound like how *this
speaker* would say it?"

The subject tier is a **parallel, independently activated tier**. It
does not replace or depend on the author tier — a memoir may declare
both (an author persona for the narration + subjects for the
dialogue); a case study may declare subjects only. A `subjects`-only
`voice:` block keeps `VoiceDocs.is_empty == True` (the author tier
stays inactive) while activating the subject tier via
`VoiceDocs.has_subjects` / `resolve_subject_voice_docs`.

### Scope boundary (vs. claim provenance, #597)

This tier owns **voice/cadence fidelity only** — does the rendered line
match the speaker's recorded register, rhythm, vocabulary, and
characteristic patterns? It does **not** own whether the underlying
facts/events actually appear in the transcript corpus (dates, names,
memories) — that substance-verification half is issue #597's claim→
source map. The touchstone for a line "She said X": #597 asks *did she
say something like X in the transcripts?*; this tier asks *does the
reconstructed line sound like how she would say it?* **Misattribution**
sits at the boundary and this tier owns it **as a voice-identity
failure** (one speaker's corpus does not match the line attributed to
them, or matches another speaker's corpus more strongly) — NOT the
substance-level "the event belongs to a different speaker's testimony"
(that is #597).

### BRIEF grammar

```yaml
voice:
  # ... optional author-tier keys (style_guide / values / corpus …) …
  subjects:
    - name: grani                          # speaker id (findings + summary)
      corpus: transcripts/grani/**/*.md    # spoken ground truth (glob)
      voice_doc: planning/grani-voice.md   # optional — cadence + failure modes
    - name: aunt-jo
      corpus: transcripts/aunt-jo/**/*.md  # voice_doc optional — corpus alone activates
```

- `name` — required, non-empty. Used verbatim in review findings and
  the `subject_voice_grounding` `_summary.md` block.
- `corpus` — required glob of transcript files. **Same resolution
  semantics as the author `corpus`**: project-root first, then
  consumer-root; `**` supported; matches sorted; a root "hits" on ≥1
  file. A glob matching zero files is `missing: true`.
- `voice_doc` — **optional** single path to a markdown doc documenting
  the speaker's cadence rules, characteristic openers ("Well,", "I'll
  tell you"), and named failure modes (e.g. "an em-dash inside a spoken
  line is a strong drift signal; balanced multi-clause sentences are
  polish creep"). Corpus alone is sufficient to activate the entry.

Resolve with
`anvil/lib/project_brief.py::resolve_subject_voice_docs(project_dir,
consumer_root=None)` — do not re-implement the walk. It returns one
`ResolvedSubjectVoice` per declared subject, in declared order, each
bundling a resolved `corpus` (`ResolvedVoiceDoc`, `kind='subject_corpus'`)
and an optional resolved `voice_doc` (`ResolvedVoiceDoc`,
`kind='subject_voice_doc'`, or `None` when the entry declared none).

### Activation (byte-identical when absent)

- **No `subjects` list (or `subjects: []`) → byte-identical.** No block,
  no findings, no `_progress.json` field, no extra reads.
  `resolve_subject_voice_docs` returns `[]`; callers branch on
  `if not resolved:` for the inactive path, exactly as the author tier
  branches on `is_empty`.
- **Declared-but-missing corpus or voice_doc → the tier ACTIVATES** and
  the breakage surfaces as a **`major` review finding** (structured
  `missing: true` entry, never a raise — the same defect-to-surface
  posture as the author tier).

### Drafter contract

When the subject tier is active, the drafter, before writing any
reconstructed dialogue:

1. **Notes which subjects appear in the draft** and loads each such
   subject's `corpus` + `voice_doc` (when present) — the spoken ground
   truth for that speaker's register.
2. **Records the consulted transcript paths in `_progress.json`** under
   `metadata.subject_voice_exemplars` — a **per-subject map**
   `{"<name>": ["<transcript path>", …], …}` — so the reviewer can
   check that grounding actually happened. No `subjects` list → the
   field is omitted entirely.

Missing declared corpora do not block drafting: the drafter proceeds
with whatever resolved, and the reviewer surfaces the broken
declaration.

### Reviewer contract

When the subject tier is active, the reviewer runs a **per-subject
voice-fidelity pass** as a sub-step within its owned voice dimension
(essay: dim 2 *Voice fidelity*). Rules mirror the author-tier
discipline, pointed at each speaker's transcript:

- **Every subject-voice deduction MUST quote the transcript** showing
  the speaker's actual cadence **alongside the drifting reconstructed
  line.** Quote the transcript, quote the drifting line. Vague feedback
  ("doesn't sound like her") without a transcript quote is itself a
  defective finding — the same load-bearing evidence discipline as the
  author corpus-quote rule.
- **The convergence-with-Claude check generalizes**: for each
  reconstructed line, the reviewer asks — *would I, the AI, also write
  this line for this speaker?* If yes, scrutinize harder, never defend.
  A polished, balanced multi-clause sentence where the transcript shows
  clipped declaratives is the canonical failure mode — model polish
  displacing the speaker's actual rhythm.
- **Misattribution is a critical flag** (**conditional: ≥2 subjects
  declared**). When a line attributed to Subject A carries
  characteristic markers that match Subject B's corpus and contradict
  Subject A's corpus, it is a critical-flag candidate. This is the
  **voice-identity failure only** (wrong voice in the wrong mouth) — the
  substance-level "the event belongs to another speaker's testimony" is
  #597 territory, NOT this flag. The justification quotes: (1) the
  attributed line, (2) the Subject A corpus showing why it does not fit,
  and (3) when identifiable, the Subject B corpus showing why it does.
  The flag routes through the skill's **existing** critical-flag
  machinery (same `Verdict.BLOCK` consequence) — it is an *additive*
  flag, not a rubric-total change.

### `_summary.md` block

When the subject tier is active, the reviewer's `_summary.md` carries a
top-level `subject_voice_grounding` block (parallel to
`voice_grounding`):

```json
"subject_voice_grounding": {
  "ran": true,
  "subjects": [
    {
      "name": "grani",
      "corpus_files_loaded": 12,
      "voice_doc_loaded": true,
      "exemplars_quoted": 3,
      "lines_flagged": 1
    }
  ]
}
```

`corpus_files_loaded` counts the resolved transcript paths read;
`voice_doc_loaded` is whether a `voice_doc` resolved (present +
non-missing); `exemplars_quoted` counts the transcript passages quoted
across that subject's voice findings; `lines_flagged` counts the
reconstructed lines deducted for that subject. When a subject's corpus
or voice_doc was declared-but-missing, add a `"missing": ["<declared
path>", …]` list on that subject entry (the `major` finding carries the
remediation).

**When the subject tier is inactive (no `subjects` list), the block is
NOT emitted at all** — no `{ran: false}` entry, byte-identical to
pre-#598 output. Same activation convention as the author-tier
`voice_grounding` block above.

### Reviser contract (one line)

The one-line author-tier reviser rule **extends to subject voices**:
when the subject tier is active, the reviser reads the resolved subject
corpora + voice docs alongside the critic feedback and **preserves the
subject voice signatures the reviewer flagged as working** — a
reconstructed line the reviewer marked as corpus-faithful must not be
sanded into model polish while chasing rubric points.

### Out of scope for #598

Substance/provenance tracing (→ #597); paper and report skill adoption
(follow-on: same lib, same pattern — their voice-grounding steps
already exist in `report-review.md` step 4d and `paper-draft.md`); audit
hooks (essay has no audit command); rhetoric-lint integration for
subject-dialogue lines (the lint's token-level rules apply to author
prose; subject dialogue is a different register); a `vocab_reminder.py`
equivalent for subject cadence. The **essay skill is the pilot
consumer** (drafter + reviewer + reviser wired below).

## Adoption

Skills adopt this contract by wiring three touch-points: an advisory
load + exemplar record in the drafter command, a triggered suffix on
the owned dimension + the `_summary.md` block in the reviewer command,
and the one-line read-and-preserve rule in the reviser command. The
memo skill is the pilot consumer (issue #461); the essay skill (issue
#460) is the first heavy consumer — its rubric weights voice much
higher, but it consumes this contract, it does not redefine it.
