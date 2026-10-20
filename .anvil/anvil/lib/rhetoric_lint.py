"""Deterministic rhetoric lint (anti-trope / banned-phrase / AI-tell scan).

Anvil's rubric dim 9 (*Rhetorical economy*) is judged by critics but was
never linted. This module adds a deterministic **rhetoric lint** to the
pre-flight family ("deterministic pre-flight before judgment" is a core
anvil principle): rule-set-driven phrase/trope/AI-tell scanning over body
markdown, producing **advisory** findings that downstream consumers (the
memo render gate's ``memo_rhetoric_lint`` dimension, issue #463) surface
as mechanical evidence for dim 9 scoring. Rhetoric rules have irreducible
false positives (quoted material, deliberate style), so this lint never
blocks: findings are warning severity at most, and the judgment call
stays with the dim 9 critics.

The rule-set SHAPE reimplements draftwell's ``packages/styleguide/``
named-rule-set model in pure stdlib Python (no TypeScript port). Five
rule kinds:

- ``phrase`` — a case-insensitive, word-boundary literal. Straight
  apostrophes in the pattern also match the typographic apostrophe
  (``'`` matches ``’``).
- ``regex`` — compiled as written, with ``re.IGNORECASE`` applied
  (the lint is a vocabulary check; casing never changes the verdict).
- ``frequency`` — a ``re.IGNORECASE`` pattern whose match count is
  measured per 1000 words of scanned text against
  ``max_per_1000_words``. A single-literal pattern behaves like a token
  count (e.g. the em-dash density rule: more than 8 ``—`` per 1000 words
  is the documented AI-tell); a span pattern counts spans (e.g. the
  ``emphasis-density`` rule counts ``\\*\\*[^*]+\\*\\*`` bold spans, more
  than ~20 per 1000 words being the bold-inflation tell). An optional
  ``label`` supplies a human name for the counted unit in the finding's
  diagnostic tail. A ``min_words`` floor (default
  :data:`DEFAULT_FREQUENCY_MIN_WORDS`) keeps density estimates from
  firing on statistically tiny texts.
- ``long_sentence`` — a syntactic-complexity sibling of ``frequency``
  (issue #750): naive sentence tokenization (split the scanned text on
  ``[.!?]`` followed by whitespace — the same fidelity the lint already
  accepts for word counts, so abbreviation noise like "Dr. Smith" is
  tolerated rather than specially handled) counts sentences whose word
  count exceeds ``sentence_word_threshold`` (default
  :data:`DEFAULT_LONG_SENTENCE_WORD_THRESHOLD`, 40 words), then measures
  that count per 1000 words against ``max_per_1000_words`` exactly like
  ``frequency``. This exists because de-hedging/de-bolding a revision
  can push qualifications out of markup (bold, parentheticals) and into
  syntax (absorbed clauses) — a pathology no markup-density rule can
  see. Deliberately **not** a mean-sentence-length cap: mean length is
  style, the pathology is the tail of multi-clause sentences a reader
  must re-parse, and the tail is what this rule measures. Shares
  ``min_words`` (the frequency floor) with the ``frequency`` kind.
- ``sentence_variance`` — a rhythm-uniformity sibling of
  ``long_sentence`` (issue #921), reusing the same naive sentence
  tokenization (:func:`_sentence_word_counts`, computed once per
  document and shared with ``long_sentence`` when both are active).
  Where ``long_sentence`` measures the *tail* (how many individual
  sentences are pathologically long), ``sentence_variance`` measures
  the *shape* of the whole distribution: the coefficient of variation
  (population stdev / mean) of sentence word counts. A document can
  pass ``long_sentence`` cleanly — no single sentence is too long —
  while every sentence still runs a near-identical length, the
  flattened-rhythm failure mode neither ``long_sentence`` nor any
  markup-density rule can see. The rule fires when the CV falls
  **below** ``min_cv`` (default :data:`DEFAULT_SENTENCE_VARIANCE_MIN_CV`)
  — the inverse polarity of every other density rule in this module,
  which fire above a ceiling. Two sample-size floors guard against a
  degenerate statistic on small texts: ``min_words`` (shared with
  ``frequency``/``long_sentence``) and ``min_sentences`` (default
  :data:`DEFAULT_SENTENCE_VARIANCE_MIN_SENTENCES`) — a single sentence
  makes the CV trivially zero (stdev of one value is zero), and a
  handful of sentences makes it unstable, so both are required before
  the rule evaluates. This is a **readability/rhythm** signal, the
  same justification ``long_sentence``'s docstring already uses (a
  reader who is handed sentence after sentence of identical shape
  starts skimming, not reading) — it is deliberately **not** shipped,
  documented, or tunable as an AI-detector-burstiness-evasion knob;
  consumers who want to defeat a detector's "burstiness" heuristic get
  no support for that from this module, and any patch that reframes
  this rule (or its calibration) around detector evasion should be
  rejected on sight.
- ``comma_stack`` — a per-sentence structural sibling of
  ``long_sentence``/``sentence_variance`` (issue #1182), reusing the
  same sentence tokenization (:func:`_sentence_chunks`, the text-
  preserving generalization ``_sentence_word_counts`` now delegates
  to). Detects "comma role-stacking": a single sentence whose commas
  are doing more than one grammatical job at once (coordinating
  clauses, opening a subordinate clause, *and* bracketing an
  appositive) — the predictable failure mode of demoting a
  dash-bracketed appositive to a comma pair under an
  em-dash-avoidance policy (see the issue for the real published
  sentence that motivated this rule). Two deterministic tiers, no
  parser required:

  1. **Hard** — a blunt ceiling, structurally identical to
     ``long_sentence``: a sentence with ``max_commas`` or more commas
     (default :data:`DEFAULT_COMMA_STACK_MAX_COMMAS`) *and*
     ``min_words`` or more words (default
     :data:`DEFAULT_COMMA_STACK_MIN_WORDS`) fires on its own, no
     pattern match required. NOTE: unlike every other kind's
     ``min_words`` (a document-level floor gating whether the rule
     evaluates at all), ``comma_stack``'s ``min_words`` is a
     **per-sentence** word count — there is no document-level floor
     for this kind, since each sentence is judged independently.
  2. **Refined** — fires at a lower comma count (``refined_min_commas``,
     default :data:`DEFAULT_COMMA_STACK_REFINED_MIN_COMMAS`) when the
     sentence, split on commas into spans, has an *interior* span (not
     the sentence-initial or sentence-final span) of 3-12 words that
     either opens with an appositive-opener token (``how``, ``what``,
     ``whether``, ``that is``, ``i.e.``, ``namely``, ``say``) or is
     immediately followed by a finite-verb candidate (``is``, ``are``,
     ``seems``, ...) — the shape of an appositive wedged between a
     subject and its verb — *and* the sentence carries a subordinator
     (``because``, ``which``, ``although``, ``while``, ``so that``)
     somewhere outside that span. A serial-list guard skips sentences
     whose interior spans are 3+ and near-uniform in length with no
     subordinator present, so ``a, b, c, and d`` never fires the
     refined tier on span shape alone.

  Quoted dialogue and code spans are excluded the same way every other
  kind is: this rule runs over the already-``_scannable_lines``-masked,
  link-collapsed text, with no additional quote-specific logic (none of
  the sibling patternless kinds have one either). Like its siblings,
  findings are document-level (``line=None`` — a sentence can wrap
  multiple source lines and per-line suppression has no defined meaning
  here); the finding's ``match`` field carries a truncated excerpt of
  the offending sentence instead. This is a **lint only** (surface +
  message), never an auto-fix — the correct repair (promote the
  appositive to its own sentence, subject position, or parentheses) is
  structural and belongs to the writer/reviewing skill, not this
  module.

JSON rule-set schema (consumer files)
-------------------------------------

Consumer rule files are JSON with this shape (identical to the dict
shape of :data:`DEFAULT_RHETORIC_RULES`, so this module is
self-documenting for consumer files)::

    {
      "name": "consumer-rules",
      "rules": [
        {"id": "no-delve", "kind": "phrase", "pattern": "delve",
         "message": "...", "severity": "warning"},
        {"id": "no-tapestry", "kind": "regex",
         "pattern": "\\\\btapestr(y|ies)\\\\b", "message": "..."},
        {"id": "no-opening-emdash", "kind": "regex", "scope": "first-line",
         "pattern": "[—–]", "message": "..."},
        {"id": "em-dash-density", "kind": "frequency", "pattern": "—",
         "max_per_1000_words": 8, "message": "..."},
        {"id": "long-sentence-density", "kind": "long_sentence",
         "sentence_word_threshold": 40, "max_per_1000_words": 4,
         "message": "..."},
        {"id": "sentence-variance-floor", "kind": "sentence_variance",
         "min_cv": 0.35, "message": "..."},
        {"id": "comma-role-stacking", "kind": "comma_stack",
         "max_commas": 5, "min_words": 25, "refined_min_commas": 4,
         "message": "..."},
        {"id": "no-internal-jargon", "kind": "regex",
         "sources_block_exempt": True,
         "pattern": "\\\\bTBD-INTERNAL\\\\b", "message": "..."}
      ],
      "disable": ["<default-rule-id>", "..."]
    }

Positional scope: ``phrase`` and ``regex`` rules accept an optional
``scope`` key. The default ``"body"`` evaluates the rule on every
non-excluded line (the original behavior). ``"first-line"`` restricts
the rule to the document's **first prose line** — the first non-blank
body line after skipping a leading YAML front-matter block and any
heading lines (layered on top of the fenced-code / comment / inline-code
exclusions). This makes document-positional tells expressible: e.g. the
``no-opening-emdash`` default fires on an em-dash in the opening line
regardless of overall density, but not on the same em-dash mid-document.
Unknown or absent ``scope`` coerces to ``"body"``. ``scope`` is
meaningless for ``frequency`` rules (frequency is always document-level)
and is not stored on them.

Sources-block exemption: ``phrase`` and ``regex`` rules accept an
optional boolean ``sources_block_exempt`` key (default ``False``,
issue #751). When ``True``, lines inside a ``Sources`` heading section
(any ATX heading ``#``..``####`` whose text is exactly ``Sources``,
case-insensitive — the memo apparatus convention documented in
``anvil.skills.memo.lib.migrate``'s ``## Sources`` parser; the section
runs to the next heading of equal or higher level) are excluded from
that rule's matching, regardless of ``scope``. This lets a rule police
body prose while treating a legitimate apparatus section — e.g. a
Sources / references block that intentionally carries internal
provenance-grade tags — as its documented home rather than a leak. The
default ``no-grade-tags-in-body`` rule (below) is the first consumer.

Merge semantics: consumer rules are appended to the framework defaults;
a consumer rule whose ``id`` collides with a default **replaces** it;
``disable`` switches off rules by id. ``severity`` defaults to
``"warning"``; consumers may downgrade to ``"info"`` but never upgrade
to ``"error"`` — an ``"error"`` (or any unknown severity) is coerced
back to ``"warning"`` because the dimension is advisory by contract.

Voice-sample precedence (a per-project override, not a framework
default change)
----------------------------------------------------------------

The default rule set encodes a **generic** AI-tell prior: most AI-drafted
prose over-uses certain patterns (em dashes among them), so
``em-dash-density`` / ``no-opening-emdash`` fire by default. That prior
is *wrong* for a specific author whose own writing genuinely favors the
flagged pattern at a measurable frequency — a real human stylistic
signature, not an AI tell, for that author. The documented resolution
is the **voice-sample precedence** pattern: when a project's
voice-grounding corpus (the ``values`` → ``style_guide`` → ``vocabulary``
→ ``corpus`` resolution order documented in
:mod:`anvil.lib.snippets.voice_grounding`, issue #461) shows the flagged
pattern occurring at that frequency in the author's own published
exemplars, the consumer supplies a project-local ``voice.rhetoric_rules``
file (resolved by
:func:`anvil.lib.project_brief.resolve_rhetoric_rules`, issue #468) that
``disable``\\ s the specific default rule id(s) for that project.

This is **not** a request to loosen the framework default — the default
stays generically correct for every project that has not made this
declaration. It is a **per-project opt-out**, scoped by the existing
``disable`` merge semantics above, and it composes with the
voice-grounding contract rather than duplicating it: the corpus already
resolved for judgment-side voice calibration is the same evidence a
consumer inspects before deciding to disable a lint rule for their own
project.

**Worked example (the canonical em-dash case, mirroring the
``blader/humanizer`` one-sentence rule — "if a user's writing sample
uses em dashes at a measured frequency, keep them at roughly that
frequency instead of scrubbing them per the generic ban"):** a project
whose ``voice.corpus`` exemplars show sustained em-dash use above the
default 8-per-1000-words ceiling declares, in the file referenced by
``voice.rhetoric_rules``::

    {
      "name": "project-rhetoric-overrides",
      "rules": [],
      "disable": ["em-dash-density", "no-opening-emdash"]
    }

With that file resolved, both em-dash rules are switched off for this
project's lint runs; every other project consuming the framework
defaults keeps scrubbing em dashes exactly as before.

Graceful degradation: malformed consumer JSON (unparseable file, or a
top-level shape that is not the documented object) produces a
defaults-only run plus ONE warning finding naming the parse error (the
``customer_context.py`` broken-declaration posture: a broken
declaration is surfaced, not silently ignored). An individually
malformed rule inside an otherwise valid file is skipped with a
warning finding naming the rule; the remaining rules still apply.

Scan exclusions
---------------

Fenced code blocks (``` / ~~~), HTML comments (including multi-line),
and inline code spans are excluded from the scan: code samples must not
fire the lint, and the suppression directive must not self-match.

Markdown link targets are also collapsed before word/sentence
measurement (issue #889): ``[text](url)`` becomes ``text``. A reader
never reads the URL, so a link-dense body must not move the
word-count denominator or the ``long_sentence`` sentence-length
measurement just because links were added or removed with no
reader-visible prose change. The collapse runs across the whole
document (not per line), so a link whose bracket text spans a hard
line wrap — the normal shape of hard-wrapped prose these skills
target — is collapsed too. See :func:`_collapse_markdown_links`.

Suppression
-----------

Per-line suppression follows the established ``anvil-lint-disable``
contract (marp_lint / memo_image_refs / render_gate): a directive of
the form ``<!-- anvil-lint-disable: memo_rhetoric_lint -->`` on the
same line as a hit, or on the line directly above it, downgrades that
line's phrase/regex hits to info findings (surfaced, not hidden).
Frequency findings are document-level (no line) and have no per-line
suppression surface; consumers tune or ``disable`` the rule instead.

Default rule set
----------------

:data:`DEFAULT_RHETORIC_RULES` is the in-module default set (the
``DEFAULT_PLACEHOLDER_PATTERNS`` precedent): conservative,
high-confidence AI-tells (grown from ~30 to ~50 in issue #920, which
adopted bucket (a) of the #919 AI-humanizer-corpus mining report by
combining thematically related candidates under a shared id — see the
issue #920 rules below for the full batch). Inclusion bar: the phrase
must be (a) a documented LLM-overuse marker and (b) rare in competent
human business/technical prose. Common discourse markers (``moreover``,
``furthermore``, ``however``) are explicitly excluded — too many false
positives on good prose.

The ``no-grade-tags-in-body`` default (issue #751) is a narrower,
register-discipline rule rather than an AI-tell: it flags an internal
evidence-grade taxonomy (``[SOLID]``, ``[DERIVED]``, ``[ASSUMPTION]``,
``[ESTIMATE ...]``, ``[MEDIUM]``/``[HIGH]``/``[LOW]``) leaking into
body prose — provenance metadata that belongs in the Sources block /
an exhibit ledger / a ``refs/`` stub, never inline (see
``anvil/skills/memo/rubric.md`` §"Dim 8 — voice-grounding calibration"
§"Grade-tag leakage (issue #751)"). It sets ``sources_block_exempt:
True`` so the Sources block itself — the tag's documented home — never
self-triggers the rule.

Public API
----------

- ``lint_rhetoric(text, *, extra_rules=None, extra_rules_path=None)``
  → :class:`RhetoricLintResult` (mirrors ``marp_lint.LintResult``:
  findings list + ``to_json()``). Standalone-callable so review-phase
  commands and non-render_gate skills can adopt without the gate.
- ``DEFAULT_RHETORIC_RULES`` — the framework default rule set.

Pure stdlib (``re``, ``json``, ``dataclasses``, ``pathlib``) — no
pydantic, no third-party imports (issue #463 acceptance criterion).
"""

from __future__ import annotations

import json
import re
import statistics
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, Sequence, Union


# Rule kinds ------------------------------------------------------------------

RULE_KIND_PHRASE = "phrase"
RULE_KIND_REGEX = "regex"
RULE_KIND_FREQUENCY = "frequency"
RULE_KIND_LONG_SENTENCE = "long_sentence"
RULE_KIND_SENTENCE_VARIANCE = "sentence_variance"
RULE_KIND_COMMA_STACK = "comma_stack"
_VALID_KINDS = (
    RULE_KIND_PHRASE,
    RULE_KIND_REGEX,
    RULE_KIND_FREQUENCY,
    RULE_KIND_LONG_SENTENCE,
    RULE_KIND_SENTENCE_VARIANCE,
    RULE_KIND_COMMA_STACK,
)
# Kinds with no ``pattern`` key: they measure document-level statistics
# (sentence-length tail / distribution shape / per-sentence comma
# structure) rather than matching text.
_PATTERNLESS_KINDS = (
    RULE_KIND_LONG_SENTENCE,
    RULE_KIND_SENTENCE_VARIANCE,
    RULE_KIND_COMMA_STACK,
)

# Severities. The dimension is advisory by contract: ``warning`` is the
# ceiling. Anything else (notably ``"error"``) is coerced to ``warning``.
SEVERITY_WARNING = "warning"
SEVERITY_INFO = "info"
_VALID_SEVERITIES = (SEVERITY_WARNING, SEVERITY_INFO)

# Pseudo-rule id used for configuration problems (malformed consumer
# JSON, invalid individual rules). Config findings are warning severity
# so a broken declaration is surfaced, not silently ignored.
CONFIG_RULE_ID = "rhetoric_lint_config"

# Frequency rules need a minimum corpus before a per-1000-words density
# is meaningful (1 em-dash in a 40-word abstract is 25/1000 — noise,
# not signal). Rule-overridable via the ``min_words`` key.
DEFAULT_FREQUENCY_MIN_WORDS = 50

# Em-dash density ceiling for the default frequency rule. The
# consumer's own em-dash counting precedent (rjwalters.info
# VOCABULARY.md): sustained density above 8 per 1000 words is the
# documented AI-tell in business/technical prose.
EMDASH_MAX_PER_1000_WORDS = 8

# Bold-emphasis density ceiling for the default ``emphasis-density``
# frequency rule (issue #745). Studio calibration: across 105 memo
# bodies the median bold density runs ~10-12 spans/1000 words on healthy
# memos; the revise loop was observed monotonically densifying one thread
# to 35+ spans/1000 (25.5% of words bolded) with no existing lint able to
# see it. 20 gives comfortable headroom above the healthy median while
# flagging the pathological 35+ range where emphasis inverts (the reader
# learns to ignore bold entirely).
EMPHASIS_MAX_PER_1000_WORDS = 20

# Long-sentence-density defaults (issue #750). The studio canary (sentinel
# memo.4 -> memo.5) demonstrated that de-hedging/de-bolding a revision can
# push qualifications out of markup and into syntax: deleting a
# parenthetical caveat and absorbing its content into the host sentence
# produces better prose AND a longer sentence, so every markup-density
# rule improves while sentence complexity quietly worsens. 40 words is the
# documented "forces a re-parse" bar; memo.5 (a genuinely improved rewrite)
# ran ~4.5 such sentences per 1000 words, a readable memo runs 1-3, so 4
# gives headroom above the healthy range while catching the pathological
# tail. Deliberately not a mean-length cap — see the module docstring.
DEFAULT_LONG_SENTENCE_WORD_THRESHOLD = 40
LONG_SENTENCE_MAX_PER_1000_WORDS = 4

# Sentence-variance-floor defaults (issue #921). Calibrated by computing the
# coefficient of variation (population stdev / mean) of naive sentence word
# counts over the repo's real anvil-authored worked-example bodies (the
# `.N/` version-dir prose across essay, primer, memoir, spec,
# ip-uspto-provisional, ip-uspto, installation, proposal, and datasheet
# examples, plus the memo BRIEF templates and the clean-memo test fixture) —
# NOT the humanizer-repo corpus mined in #919, which is uncalibrated
# guidance, not a threshold. Every one of those genuine-prose documents with
# >=50 words measured CV >= 0.413 (lowest: a short attribution memo body),
# with most well above 0.5 and several long documents exceeding 1.0. A
# document artificially flattened to the failure mode this rule targets —
# every sentence landing in an 18-22 word band, the shape #919's mining
# report calls out — measures CV ~0.08; even a looser 15-25 word band
# measures ~0.16. 0.35 sits with clear headroom below the observed
# real-prose floor (~18% below the lowest genuine sample) while sitting
# well above the pathological-uniformity range, mirroring how
# DEFAULT_LONG_SENTENCE_WORD_THRESHOLD was picked with headroom above a
# healthy range and below an observed pathological one. Two sample-size
# floors avoid a degenerate statistic on tiny texts: `min_words` (shared
# with `frequency`/`long_sentence`) and `min_sentences` below — a
# single-sentence text has stdev zero by construction (CV = 0), which
# would otherwise always fire. `min_sentences` = 6 was picked directly
# against this same corpus: a 5-sentence, 88-word test fixture (an
# edge-case BRIEF.md, not representative prose at any meaningful scale)
# measured CV 0.346 — inside noise distance of the 0.35 floor purely
# because 5 data points is too small a sample for the statistic to be
# stable — while every corpus document with >=6 sentences cleared the
# floor with real margin.
DEFAULT_SENTENCE_VARIANCE_MIN_CV = 0.35
DEFAULT_SENTENCE_VARIANCE_MIN_SENTENCES = 6

# Comma-role-stacking defaults (issue #1182), literally from the Proposal
# spec text: the hard tier's ceiling ("max_commas or more commas ... and
# min_words or more words") and the refined tier's lower comma floor
# ("fires at lower comma counts"). NOTE: unlike the document-level
# `min_words` shared by `frequency`/`long_sentence`/`sentence_variance`,
# DEFAULT_COMMA_STACK_MIN_WORDS gates a single sentence's own word count —
# there is no document-level floor for this kind (see the module
# docstring's `comma_stack` bullet).
DEFAULT_COMMA_STACK_MAX_COMMAS = 5
DEFAULT_COMMA_STACK_MIN_WORDS = 25
DEFAULT_COMMA_STACK_REFINED_MIN_COMMAS = 4

# Suppression-directive rule tokens honored by default. The memo gate's
# dimension name is the documented consumer-facing token
# (``<!-- anvil-lint-disable: memo_rhetoric_lint -->``); the generic
# ``rhetoric_lint`` token works for standalone (non-gate) callers.
DEFAULT_SUPPRESS_RULES: tuple[str, ...] = (
    "memo_rhetoric_lint",
    "rhetoric_lint",
)


# Default rule set --------------------------------------------------------------
#
# Conservative, high-confidence AI-tells only (curation Decision 2,
# issue #463). Every entry is calibrated against the repo's memo-prose
# corpus (templates + fixture memo bodies) — the enforced
# zero-findings-on-good-prose bar in tests/lib/test_rhetoric_lint.py.
DEFAULT_RHETORIC_RULES: tuple[dict, ...] = (
    {
        "id": "no-delve",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bdelv(e|es|ed|ing)\b",
        "message": "'delve' is a documented LLM-overuse marker; prefer a plain verb (examine, explore, look at).",
    },
    {
        "id": "no-tapestry",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\btapestr(y|ies)\b",
        "message": "'tapestry' (rich tapestry, tapestry of ...) is a documented AI-tell metaphor; say what the parts actually are.",
    },
    {
        "id": "no-important-to-note",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bit(?:['’]s| is) important to note\b",
        "message": "'it's important to note' is filler; if it matters, state it directly.",
    },
    {
        "id": "no-worth-noting",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bit(?:['’]s| is) worth noting\b",
        "message": "'it's worth noting' is filler; if it's worth noting, just note it.",
    },
    {
        "id": "no-fast-paced",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bin today['’]s fast-paced\b|\bfast-paced (?:world|environment|landscape|digital)\b",
        "message": "'in today's fast-paced ...' is an AI-tell opener; cut the throat-clearing and lead with the claim.",
    },
    {
        "id": "no-testament-to",
        "kind": RULE_KIND_PHRASE,
        "pattern": "a testament to",
        "message": "'a testament to' is an AI-tell intensifier; show the evidence instead of labeling it.",
    },
    {
        "id": "no-end-of-the-day",
        "kind": RULE_KIND_PHRASE,
        "pattern": "at the end of the day",
        "message": "'at the end of the day' is a hedge-cliché; state the conclusion without the ramp.",
    },
    {
        "id": "no-serves-as-a",
        "kind": RULE_KIND_PHRASE,
        "pattern": "serves as a",
        "message": "'serves as a' is indirection; prefer 'is' or the concrete verb.",
    },
    {
        "id": "no-crucial-role",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bplay(?:s|ed|ing)? a (?:crucial|vital|pivotal|key) role\b",
        "message": "'plays a crucial/vital role' is an AI-tell construction; name what the thing actually does.",
    },
    {
        "id": "no-seamless",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bseamless(?:ly)?\b",
        "message": "'seamless(ly)' is marketing filler and a documented LLM marker; describe the actual integration behavior.",
    },
    {
        "id": "no-navigate-complexities",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bnavigat(?:e|es|ed|ing) the complexit(?:y|ies)\b",
        "message": "'navigate the complexities' is an AI-tell metaphor; name the specific difficulty.",
    },
    {
        "id": "no-realm-of",
        "kind": RULE_KIND_PHRASE,
        "pattern": "in the realm of",
        "message": "'in the realm of' is an AI-tell scoping phrase; prefer 'in' or name the field plainly.",
    },
    {
        "id": "no-multifaceted",
        "kind": RULE_KIND_PHRASE,
        "pattern": "multifaceted",
        "message": "'multifaceted' is a documented LLM marker; enumerate the facets instead.",
    },
    {
        "id": "no-underscores-verb",
        "kind": RULE_KIND_REGEX,
        # Inflected verb forms only — the bare noun "underscore" (the
        # character) is deliberately excluded for technical prose.
        "pattern": r"\bunderscor(?:es|ed|ing)\b",
        "message": "'underscores the ...' is an AI-tell verb; prefer 'shows', 'confirms', or drop the sentence.",
    },
    {
        "id": "no-ever-evolving",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bever-(?:evolving|changing)\b",
        "message": "'ever-evolving/ever-changing' is an AI-tell modifier; cut it or cite the actual change.",
    },
    {
        "id": "no-embark-journey",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bembark(?:s|ed|ing)? (?:up)?on a journey\b",
        "message": "'embark on a journey' is an AI-tell metaphor; say what is starting.",
    },
    {
        "id": "no-harness-power",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bharness(?:es|ed|ing)? the power of\b",
        "message": "'harness the power of' is marketing filler; name the capability being used.",
    },
    {
        "id": "no-unlock-potential",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bunlock(?:s|ed|ing)? the (?:full )?(?:potential|power)\b",
        "message": "'unlock the potential/power' is marketing filler; state the concrete benefit.",
    },
    {
        "id": "no-goes-without-saying",
        "kind": RULE_KIND_PHRASE,
        "pattern": "it goes without saying",
        "message": "'it goes without saying' — then don't say it, or say it without the preamble.",
    },
    {
        "id": "no-myriad-of",
        "kind": RULE_KIND_PHRASE,
        "pattern": "a myriad of",
        "message": "'a myriad of' is an AI-tell quantifier; give a number or say 'many'.",
    },
    {
        "id": "no-plethora",
        "kind": RULE_KIND_PHRASE,
        "pattern": "plethora",
        "message": "'plethora' is a documented LLM marker; give a number or say 'many'.",
    },
    {
        "id": "no-look-no-further",
        "kind": RULE_KIND_PHRASE,
        "pattern": "look no further",
        "message": "'look no further' is marketing copy; state the recommendation directly.",
    },
    {
        "id": "no-meticulously-x",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bmeticulously (?:crafted|designed|curated)\b",
        "message": "'meticulously crafted/designed/curated' is an AI-tell intensifier; describe the actual care taken.",
    },
    {
        "id": "no-ai-model-leak",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bas an? (?:AI|artificial intelligence)(?: language)? model\b",
        "message": "Assistant-persona leak ('as an AI model ...') — remove the chat artifact from the document body.",
    },
    {
        "id": "no-finds-you-well",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bhopes? this (?:email|message|letter|memo) finds you well\b",
        "message": "'hope this message finds you well' is boilerplate; open with the point.",
    },
    {
        "id": "no-game-changer",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bgame[- ]chang(?:er|ers|ing)\b",
        "message": "'game-changer' is hype vocabulary; quantify the change instead.",
    },
    {
        "id": "no-opening-emdash",
        "kind": RULE_KIND_REGEX,
        "scope": "first-line",
        # Unicode em-dash (U+2014) and en-dash (U+2013) only — the
        # dash-variant fold used by ``em-dash-density``. The Markdown
        # ``--``/``---`` shorthands are deliberately excluded: on the
        # first prose line they collide with a thematic break (``---``)
        # and would false-positive. Positional, not density: fires on
        # ANY opening-line em-dash regardless of overall frequency.
        "pattern": r"[—–]",
        "message": "Opening line contains an em-dash — a documented generic-AI-cadence tell; rewrite the opening without em-dashes.",
    },
    {
        "id": "em-dash-density",
        "kind": RULE_KIND_FREQUENCY,
        "pattern": "—",
        "max_per_1000_words": EMDASH_MAX_PER_1000_WORDS,
        "message": "Em-dash density exceeds the AI-tell threshold; vary punctuation (commas, colons, parentheses, periods).",
    },
    {
        "id": "emphasis-density",
        "kind": RULE_KIND_FREQUENCY,
        # A bold span: ``**...**`` with at least one non-asterisk char
        # inside. Frequency patterns are compiled as regex (case fold is
        # irrelevant here), so this counts bold *spans*, not raw ``**``
        # runs — one span == one finding-worthy unit of emphasis.
        "pattern": r"\*\*[^*]+\*\*",
        "label": "bold span",
        "max_per_1000_words": EMPHASIS_MAX_PER_1000_WORDS,
        "message": "Bold emphasis above ~20 spans/1000 words stops functioning as emphasis; reserve bold for decision-critical claims (gates, kill lines, the recommendation).",
    },
    {
        "id": "no-meta-commentary",
        "kind": RULE_KIND_REGEX,
        # Reviewer-addressed meta-commentary: prose *about* the document
        # (self-reference + a describing verb) plus the fixed
        # rubric-compliance-performance phrases the studio canary
        # surfaced ("argued here", "not re-argued here", "out of scope
        # here", "stated plainly"). The self-reference arm deliberately
        # covers both "this memo" and "the memo/document" against a broad
        # verb set — the memo.8 escape (issue #745) was a narrower grep
        # that missed "this memo proposes".
        "pattern": (
            r"\b(?:this|the) (?:memo|document) "
            r"(?:does not|do not|is|are|argues?|proposes?|claims?|"
            r"pretends?|assumes?|shows?|demonstrates?|contends?)\b"
            r"|\b(?:argued|stated|confronted) here\b"
            r"|\bre-argued here\b"
            r"|\bout of scope here\b"
            r"|\bstated plainly\b"
        ),
        "message": "Prose about the document is addressed to the reviewer, not the reader; delete the frame and keep the content.",
    },
    {
        "id": "no-warning-emoji",
        "kind": RULE_KIND_REGEX,
        # Warning / alarm emoji in body prose. The variation selector
        # (U+FE0F) rides with U+26A0 in the class; matching it alone is
        # harmless (it never appears un-anchored in real prose).
        "pattern": r"[⚠️🚨❗]",
        "message": "Emoji alarm markers are emphasis inflation; if it's a kill condition, say so in words.",
    },
    {
        "id": "long-sentence-density",
        "kind": RULE_KIND_LONG_SENTENCE,
        "sentence_word_threshold": DEFAULT_LONG_SENTENCE_WORD_THRESHOLD,
        "max_per_1000_words": LONG_SENTENCE_MAX_PER_1000_WORDS,
        "message": (
            "Long-sentence density exceeds the readability ceiling; "
            "multi-clause sentences over ~40 words force a re-parse — "
            "split them or cut a clause instead of absorbing it into the "
            "sentence."
        ),
    },
    {
        "id": "sentence-variance-floor",
        "kind": RULE_KIND_SENTENCE_VARIANCE,
        "min_cv": DEFAULT_SENTENCE_VARIANCE_MIN_CV,
        "message": (
            "Sentence-length variance is below the readability floor; "
            "a run of near-identical sentence lengths flattens rhythm and "
            "reads as monotonous — vary sentence length structurally, not "
            "just its content."
        ),
    },
    {
        "id": "comma-role-stacking",
        "kind": RULE_KIND_COMMA_STACK,
        "max_commas": DEFAULT_COMMA_STACK_MAX_COMMAS,
        "min_words": DEFAULT_COMMA_STACK_MIN_WORDS,
        "refined_min_commas": DEFAULT_COMMA_STACK_REFINED_MIN_COMMAS,
        # The leading count is prepended at finding time (not part of
        # this template) so the finding reads "N commas doing multiple
        # grammatical jobs ..." — see the ``comma_stack`` branch in
        # ``lint_rhetoric``.
        "message": (
            "commas doing multiple grammatical jobs in one sentence; if "
            "a comma pair is bracketing an interjection, fix by "
            "promotion (own sentence, subject position, or "
            "parentheses), not re-punctuation. A comma pair is not a "
            "drop-in replacement for a dash pair."
        ),
    },
    {
        "id": "no-grade-tags-in-body",
        "kind": RULE_KIND_REGEX,
        # An internal evidence-grade taxonomy leaking into body prose
        # (issue #751): a bracket opening on a grade keyword, optionally
        # followed by elaboration (e.g. "ESTIMATE from SOLID inputs" or
        # "MEDIUM: vendor research post ..."), closed by the next "]".
        # ``[^\[\]]*`` stops at a nested/adjacent bracket so an ordinary
        # citation marker like "[1]" or "[Smith 2020]" never matches (no
        # grade keyword at the open) and this rule can't swallow past a
        # real closing bracket into unrelated text.
        "pattern": r"\[(?:SOLID|DERIVED|ASSUMPTION|ESTIMATE|MEDIUM|HIGH|LOW)\b[^\[\]]*\]",
        "sources_block_exempt": True,
        "message": "Evidence-grade tag leaked into body prose; preserve the grade in the Sources block / an exhibit ledger / a refs/ stub and use a plain-language hedge in prose instead (rubric.md §\"Grade-tag leakage (issue #751)\").",
    },
    # ------------------------------------------------------------------
    # Issue #920 (bucket a of #919's AI-humanizer-corpus mining report,
    # `docs/research/919-ai-humanizer-mining.md` §"(a) Drop-in additions"):
    # 18 rules distilled from ~41 individually FP-checked candidate
    # patterns. Several thematically related candidates are combined
    # under one id via a single alternation regex — the same shape the
    # module already uses (``no-crucial-role``, ``no-fast-paced``,
    # ``no-unlock-potential`` above each cover multiple word forms under
    # one id) — trading id-per-term granularity for a bounded rule-count
    # growth (33 -> 51) rather than the 69-75 a literal one-id-per-term
    # adoption would produce. See the PR description for the full
    # count/threshold rationale.
    {
        "id": "no-copula-avoidance-cluster",
        "kind": RULE_KIND_REGEX,
        # Siblings of ``no-serves-as-a``: other copula-avoidance verbs
        # the mining report found in the same family.
        "pattern": r"\b(?:stands|functions) as (?:a|an)\b|\b(?:features|boasts) (?:a|an)\b",
        "message": "'stands as a/an', 'functions as a/an', 'features a/an', 'boasts a/an' are copula-avoidance siblings of 'serves as a'; prefer 'is' or the concrete verb.",
    },
    {
        "id": "no-align-with",
        "kind": RULE_KIND_PHRASE,
        "pattern": "align with",
        "message": "'align with' is a documented AI-vocabulary marker; name the concrete relationship instead (match, support, follow).",
    },
    {
        "id": "no-garner",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bgarner(?:s|ed|ing)?\b",
        "message": "'garner(s/ed/ing)' is a documented AI-vocabulary marker; prefer 'earn', 'win', or 'get'.",
    },
    {
        "id": "no-ai-buzzword-nouns",
        "kind": RULE_KIND_REGEX,
        # interplay / intricate(-acy/-acies) / cornerstone / paradigm /
        # synergy — combined per the mining report's own clustering.
        "pattern": r"\binterplay\b|\bintricat(?:e|acy|acies)\b|\bcornerstone\b|\bparadigm\b|\bsynergy\b",
        "message": "AI-vocabulary noun ('interplay', 'intricate(-acy)', 'cornerstone', 'paradigm', 'synergy'); name the specific relationship or mechanism instead.",
    },
    {
        "id": "no-ai-buzzword-adjectives",
        "kind": RULE_KIND_REGEX,
        # renowned / groundbreaking / nestled / robust / holistic.
        "pattern": r"\brenowned\b|\bgroundbreaking\b|\bnestled\b|\brobust\b|\bholistic\b",
        "message": "AI-vocabulary adjective ('renowned', 'groundbreaking', 'nestled', 'robust', 'holistic'); replace with a concrete, falsifiable descriptor.",
    },
    {
        "id": "no-promo-triad",
        "kind": RULE_KIND_REGEX,
        # cutting-edge / state-of-the-art / world-class — the mining
        # report's "promo triad".
        "pattern": r"\bcutting-edge\b|\bstate-of-the-art\b|\bworld-class\b",
        "message": "'cutting-edge' / 'state-of-the-art' / 'world-class' is marketing filler; name the specific capability instead.",
    },
    {
        "id": "no-superficial-ing-padding",
        "kind": RULE_KIND_REGEX,
        # highlighting / showcas(e|es|ed|ing) / reflecting /
        # symboliz(e|es|ed|ing) / foster(s|ed|ing)? — superficial
        # "-ing"-analysis padding. ('underscoring' is deliberately
        # excluded: it duplicates the existing no-underscores-verb rule
        # above.)
        "pattern": r"\bhighlighting\b|\bshowcas(?:e|es|ed|ing)\b|\breflecting\b|\bsymboliz(?:e|es|ed|ing)\b|\bfoster(?:s|ed|ing)?\b",
        "message": "Superficial '-ing'-analysis padding ('highlighting', 'showcasing', 'reflecting', 'symbolizing', 'fostering'); state the claim directly instead of gesturing at it.",
    },
    {
        "id": "no-negative-parallelism",
        "kind": RULE_KIND_REGEX,
        # "not only ... but", "not just ... but", "it's not X, it's Y" —
        # span-capped to ~80 chars and to a single sentence (no
        # terminator crossed) so the pattern cannot bridge two unrelated
        # sentences.
        "pattern": (
            r"\bnot only\b[^.!?\n]{0,80}?\bbut\b"
            r"|\bnot just\b[^.!?\n]{0,80}?\bbut\b"
            r"|\bit(?:['’]s| is) not\b[^.!?\n]{0,80}?,\s*it(?:['’]s| is)\b"
        ),
        "message": "Negative-parallelism construction ('not only... but', 'not just... but', 'it's not X, it's Y') is an AI-tell rhetorical device; state the claim plainly.",
    },
    {
        "id": "no-more-than-just",
        "kind": RULE_KIND_PHRASE,
        "pattern": "more than just",
        "message": "'more than just' is a hedge-and-inflate construction; state what it actually is.",
    },
    {
        "id": "no-fake-significance-cluster",
        "kind": RULE_KIND_REGEX,
        # indelible mark / turning point / focal point / deeply rooted /
        # evolving landscape — the mining report's "fake-significance
        # cluster".
        "pattern": r"\bindelible mark\b|\bturning point\b|\bfocal point\b|\bdeeply rooted\b|\bevolving landscape\b",
        "message": "Fake-significance phrase ('indelible mark', 'turning point', 'focal point', 'deeply rooted', 'evolving landscape') asserts importance instead of showing it; state the concrete claim.",
    },
    {
        "id": "no-sets-the-stage",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bsett?ing the stage\b",
        "message": "'setting the stage' is an AI-tell scene-setting metaphor; state what actually enables the next step.",
    },
    {
        "id": "no-it-is-believed",
        "kind": RULE_KIND_REGEX,
        "pattern": r"\bit is (?:widely )?(?:believed|considered|known|thought)\b",
        "message": "'it is (widely) believed/considered/known/thought' is unattributed weasel phrasing; name who believes it or cut the hedge.",
    },
    {
        "id": "no-sycophantic-cluster",
        "kind": RULE_KIND_REGEX,
        # Chat/assistant-artifact leak: sycophantic filler that belongs
        # in a chat transcript, not document body prose.
        "pattern": r"\bi hope this helps\b|\bgreat question\b|\byou['’]re absolutely right\b",
        "message": "Sycophantic chat-assistant artifact ('I hope this helps', 'great question', 'you're absolutely right') leaked into the document body; remove it.",
    },
    {
        "id": "no-knowledge-cutoff",
        "kind": RULE_KIND_REGEX,
        # Chat/assistant-artifact leak: knowledge-cutoff disclaimer.
        "pattern": r"\bup to my last training update\b|\bas of my (?:last|knowledge) (?:update|cutoff)\b",
        "message": "Knowledge-cutoff disclaimer ('up to my last training update', 'as of my knowledge cutoff') is a chat-assistant artifact; remove it and date the claim in-document instead.",
    },
    {
        "id": "no-copy-paste-artifact",
        "kind": RULE_KIND_REGEX,
        # Chat/assistant-artifact leak: vendor-specific citation/copy
        # markers documented on Wikipedia's "Signs of AI writing" page.
        "pattern": r"oaicite|contentReference|oai_citation|turn\d+search\d+|grok_card|attached_file",
        "message": "Copy-paste chat/assistant citation artifact leaked into the document body; remove it and replace with a real citation.",
    },
    {
        "id": "no-curly-quotes",
        "kind": RULE_KIND_FREQUENCY,
        # Typographic (curly) quote/apostrophe marks. Mirrors
        # ``em-dash-density``'s shape: a low density ceiling rather than
        # a hard ban, since a single quoted excerpt pasted from
        # elsewhere should not fire the lint.
        "pattern": r"[‘’“”]",
        "label": "curly quote",
        "max_per_1000_words": 2,
        "message": "Curly (typographic) quote marks above a low density is a documented AI-writing-tool tell in plain-markdown house style; use straight quotes/apostrophes.",
    },
    {
        "id": "no-weasel-attribution",
        "kind": RULE_KIND_REGEX,
        # Calibration fix (issue #920, found during the #919 FP check):
        # the plural-only noun group avoids matching a singular
        # "Critic" heading (e.g. "## Critic note -> change") against a
        # following verb; "note" is also dropped from the verb
        # alternation (too generic a verb to pair with a heading noun).
        "pattern": (
            r"\b(?:experts|studies|researchers|observers|critics) "
            r"(?:say|says|show|shows|argue|argues|believe|believes|"
            r"claim|claims|suggest|suggests)\b"
        ),
        "message": "Unattributed weasel attribution ('experts/studies/researchers/observers/critics say/show/argue/...'); name the actual source or cut the hedge.",
    },
    {
        "id": "hyphen-pair-density",
        "kind": RULE_KIND_FREQUENCY,
        # Calibration fix (issue #920, found during the #919 FP check):
        # end-to-end / real-time / long-term are domain-neutral
        # engineering vocabulary (they fired on "## End-to-end smoke
        # flow" dev-doc headings), not the marketing-register compounds
        # this rule targets, so they are deliberately excluded from the
        # word list.
        "pattern": (
            r"\b(?:data-driven|cross-functional|best-in-class|"
            r"future-proof|value-add|client-facing|decision-making|"
            r"third-party)\b"
        ),
        "label": "marketing-register hyphenated compound",
        "max_per_1000_words": 3,
        "message": "Marketing-register hyphenated-compound density is elevated; name the specific mechanism instead of the compound buzzword.",
    },
)


# Result types ------------------------------------------------------------------


@dataclass
class RhetoricFinding:
    """One rhetoric-lint hit (or config problem)."""

    rule_id: str
    severity: str            # "warning" | "info"
    message: str
    line: Optional[int] = None      # 1-based source line; None for document-level
    match: Optional[str] = None     # the matched text, when line-anchored

    def to_dict(self) -> dict:
        return {
            "rule_id": self.rule_id,
            "severity": self.severity,
            "message": self.message,
            "line": self.line,
            "match": self.match,
        }


@dataclass
class RhetoricLintResult:
    """Outcome of one rhetoric-lint pass.

    Mirrors ``marp_lint.LintResult``: a findings list plus
    ``to_json()``. There is no ``errors`` bucket by design — the lint
    is advisory and ``warning`` is the severity ceiling.
    """

    findings: list[RhetoricFinding] = field(default_factory=list)
    words: int = 0                       # words in the scanned (non-excluded) text
    rules_applied: list[str] = field(default_factory=list)

    @property
    def warnings(self) -> list[RhetoricFinding]:
        return [f for f in self.findings if f.severity == SEVERITY_WARNING]

    @property
    def infos(self) -> list[RhetoricFinding]:
        return [f for f in self.findings if f.severity == SEVERITY_INFO]

    @property
    def total(self) -> int:
        return len(self.findings)

    def to_json(self) -> dict:
        return {
            "lint": "rhetoric_lint",
            "words": self.words,
            "rules_applied": list(self.rules_applied),
            "warnings": len(self.warnings),
            "infos": len(self.infos),
            "findings": [f.to_dict() for f in self.findings],
        }


# Scan preprocessing ------------------------------------------------------------

# Word tokens for the per-1000-words denominator. Hyphenated and
# apostrophized compounds count once ("fast-paced", "it's").
_WORD_RE = re.compile(r"[A-Za-z0-9]+(?:['’\-][A-Za-z0-9]+)*")

# Code-fence opener/closer (``` or ~~~, up to 3 leading spaces per
# CommonMark).
_FENCE_RE = re.compile(r"^ {0,3}(```|~~~)")

# Inline code span: `...` (non-greedy, single line).
_INLINE_CODE_RE = re.compile(r"`[^`\n]*`")

# Suppression directive (mirrors render_gate._MEMO_LINT_DISABLE_RE /
# memo_image_refs): comma-separated rule list inside an HTML comment.
_LINT_DISABLE_RE = re.compile(
    r"<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->",
)

# YAML front-matter fence: a ``---`` (optionally trailing whitespace) on
# the document's very first line opens a block that runs to the next
# such line. Used by ``_first_prose_lineno`` to skip metadata before the
# first prose line.
_FRONT_MATTER_FENCE_RE = re.compile(r"^---\s*$")

# ATX heading line (``#`` … ``######`` followed by whitespace). Skipped
# when locating the first prose line — a heading is not prose.
_HEADING_RE = re.compile(r"^#{1,6}\s")

# Naive sentence boundary for the ``long_sentence`` kind (issue #750): a
# sentence terminator immediately followed by whitespace. Deliberately the
# same fidelity the module already accepts for word counts — abbreviation
# noise ("Dr. Smith", "e.g. foo") produces occasional over-splits, which is
# tolerated rather than specially handled (see the module docstring).
_SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+")

# ATX heading line, depth-capturing variant. Used by
# :func:`_sources_block_lines` to track section boundaries (needs the
# ``#`` count; ``_HEADING_RE`` above only needs a yes/no match).
_HEADING_DEPTH_RE = re.compile(r"^(#{1,6})\s")

# Markdown link: ``[text](url)`` (optional leading ``!`` for image
# links). Issue #889: a reader never reads the URL, so link targets
# must not inflate the word-count denominator or the ``long_sentence``
# word counts. The ``text`` group is allowed to contain newlines — a
# link whose bracket text spans a hard line wrap (the normal shape of
# the hard-wrapped prose these skills target) is still collapsed, not
# just the subset that happens to fit on one line. Deliberately a
# module-local pattern (not imported from ``hyperlink_resolver``) —
# this lint has no other coupling to that critic and the shape is
# small enough not to be worth a cross-module dependency.
_MD_LINK_COLLAPSE_RE = re.compile(
    r"""
    !?                                  # optional ! prefix for images
    \[(?P<text>[^\]]*)\]                # [text] -- text may span lines
    \((?:[^\s)]+)\)                     # (url) -- discarded
    """,
    re.VERBOSE,
)

# A "Sources" heading (``#``..``####`` depth — matches the memo
# apparatus convention in ``anvil.skills.memo.lib.migrate``'s
# ``## Sources`` parser). Case-insensitive; the heading text must be
# exactly "Sources" (no trailing prose) to avoid matching an unrelated
# heading that merely contains the word.
_SOURCES_HEADING_RE = re.compile(r"^#{1,4}\s+Sources\s*$", re.IGNORECASE)


def _scannable_lines(text: str) -> list[str]:
    """Per-line scan text with exclusions blanked.

    Returns one string per source line (index ``i`` ↔ source line
    ``i + 1``) with fenced code blocks, HTML comments (including
    multi-line spans), and inline code spans removed. Line count and
    line numbering are preserved so findings stay anchored to the
    original source.
    """
    out: list[str] = []
    in_fence = False
    fence_marker = ""
    in_comment = False
    for raw in text.splitlines():
        line = raw
        # --- fenced code blocks: blank the fence lines AND the body ---
        if not in_comment:
            m = _FENCE_RE.match(line)
            if m:
                if not in_fence:
                    in_fence = True
                    fence_marker = m.group(1)
                elif m.group(1) == fence_marker:
                    in_fence = False
                out.append("")
                continue
        if in_fence:
            out.append("")
            continue
        # --- HTML comments (multi-line aware) --------------------------
        if in_comment:
            end = line.find("-->")
            if end == -1:
                out.append("")
                continue
            line = line[end + 3:]
            in_comment = False
        # Strip any complete or opening comment spans on this line.
        while True:
            start = line.find("<!--")
            if start == -1:
                break
            end = line.find("-->", start + 4)
            if end == -1:
                line = line[:start]
                in_comment = True
                break
            line = line[:start] + " " + line[end + 3:]
        # --- inline code spans -----------------------------------------
        line = _INLINE_CODE_RE.sub(" ", line)
        out.append(line)
    return out


def _collapse_markdown_links(scan_lines: list[str]) -> list[str]:
    """Collapse ``[text](url)`` -> ``text`` across the joined scan text.

    Issue #889: a reader never reads the URL, so a link's target must
    not count toward the word-count denominator or the
    ``long_sentence`` sentence-length measurement. Operates on the
    full joined blob (``"\\n".join(scan_lines)``), not per individual
    line, so a link whose bracket text spans a hard line wrap is still
    collapsed — the per-line scan in :func:`_scannable_lines` would
    otherwise never see the still-open ``[`` on the first line and the
    dangling ``](url)`` on the next. Only the surrounding markup
    (``[``, ``]``, ``(url)``) is removed; any newline embedded in the
    bracket text is part of the replacement, so the total newline
    count — and therefore the line count and 1-based line numbering
    used by ``lint_rhetoric``'s per-line phrase/regex rules — is
    unchanged.
    """
    joined = "\n".join(scan_lines)
    collapsed = _MD_LINK_COLLAPSE_RE.sub(lambda m: m.group("text"), joined)
    return collapsed.split("\n")


def _sentence_chunks(scan_lines: list[str]) -> list[str]:
    """Naive per-sentence text chunks, computed once per document.

    Joins the (already-excluded) scan lines into a single blob — so a
    sentence wrapped across two source lines is not miscounted as two
    short sentences — and splits on :data:`_SENTENCE_SPLIT_RE`. Each
    resulting chunk (including a final chunk with no trailing
    terminator) is one naive "sentence". Text-preserving generalization
    of the word-count-only helper this module originally shipped
    (``_sentence_word_counts`` now delegates here) — the ``comma_stack``
    kind (issue #1182) needs the actual sentence text, not just its
    word count, to inspect comma structure.
    """
    blob = " ".join(line for line in scan_lines if line.strip())
    if not blob.strip():
        return []
    return [
        chunk.strip()
        for chunk in _SENTENCE_SPLIT_RE.split(blob.strip())
        if chunk.strip()
    ]


def _sentence_word_counts(scan_lines: list[str]) -> list[int]:
    """Word count per naive sentence, computed once per document.

    See :func:`_sentence_chunks` for the tokenization contract. Word
    counts are measured with the same :data:`_WORD_RE` tokenizer used
    for the document's overall word count, so the two counts are
    directly comparable.
    """
    return [len(_WORD_RE.findall(chunk)) for chunk in _sentence_chunks(scan_lines)]


# Comma-role-stacking detection (issue #1182) -------------------------------

# Appositive-opener tokens: a word/phrase that, opening an interior
# comma-bracketed span, marks the span as renaming/explaining the noun
# phrase just before it (an appositive) rather than continuing a list or
# an absolute phrase. Checked against the start of the span only.
_COMMA_STACK_APPOSITIVE_OPENERS: tuple[str, ...] = (
    "how",
    "what",
    "whether",
    "that is",
    "i.e.",
    "namely",
    "say",
)

# Finite-verb candidates: a linking/copula verb that, appearing as the
# first word immediately AFTER an interior span's closing comma, marks
# the span as sitting between a subject and its verb (the "X, span, is
# Y" appositive shape) rather than e.g. a serial-list item.
_COMMA_STACK_FINITE_VERBS: frozenset[str] = frozenset(
    {
        "is", "are", "was", "were",
        "seems", "seem", "remains", "remain",
        "becomes", "become", "appears", "appear",
        "looks", "look", "sounds", "sound",
        "feels", "feel", "stays", "stay",
        "proves", "prove",
    }
)

# Subordinators the refined tier requires OUTSIDE the qualifying
# appositive span — the second grammatical job the sentence's commas are
# doing (coordinating/opening a subordinate clause) beyond bracketing the
# appositive itself.
_COMMA_STACK_SUBORDINATOR_RE = re.compile(
    r"\b(?:because|which|although|while|so that)\b", re.IGNORECASE
)

# Interior-span word-count band for the refined tier's appositive check.
_COMMA_STACK_SPAN_MIN_WORDS = 3
_COMMA_STACK_SPAN_MAX_WORDS = 12

# Serial-list guard: 3+ interior spans whose word counts fall within this
# spread (max - min) are treated as list items ("a, b, c, and d"), not an
# appositive-bracketed span — regardless of whether one of them happens
# to start with an appositive-opener token.
_COMMA_STACK_SERIAL_LIST_MIN_SPANS = 3
_COMMA_STACK_SERIAL_LIST_MAX_SPREAD = 2


def _comma_stack_starts_with_opener(span: str) -> bool:
    """Whether ``span`` opens with an appositive-opener token."""
    low = span.strip().lower()
    for token in _COMMA_STACK_APPOSITIVE_OPENERS:
        if low == token or low.startswith(token + " ") or low.startswith(token + ","):
            return True
    return False


def _comma_stack_first_word(text: str) -> str:
    """Lowercased first :data:`_WORD_RE` token of ``text``, or ``""``."""
    m = _WORD_RE.match(text.strip())
    return m.group(0).lower() if m else ""


def _comma_stack_looks_like_serial_list(interior_word_counts: list[int]) -> bool:
    """Serial-list guard: 3+ near-uniform-length interior spans.

    ``interior_word_counts`` is the word count of every interior span
    (sentence-initial and sentence-final spans excluded), regardless of
    whether any individual span falls inside the appositive-check word
    band. A near-identical spread across 3+ items is the shape of a
    comma-separated list ("a, b, c, and d"), not a single bracketed
    appositive.
    """
    if len(interior_word_counts) < _COMMA_STACK_SERIAL_LIST_MIN_SPANS:
        return False
    spread = max(interior_word_counts) - min(interior_word_counts)
    return spread <= _COMMA_STACK_SERIAL_LIST_MAX_SPREAD


def _comma_stack_refined_signal(spans: list[str]) -> bool:
    """Refined-tier check over one sentence's comma-split spans.

    ``spans`` is ``sentence.split(",")`` with each fragment stripped
    (length == comma count + 1). Returns ``True`` when an interior span
    (a) sits in the 3-12 word band, (b) opens with an appositive-opener
    token or is immediately followed by a finite-verb candidate, and (c)
    the sentence carries a subordinator outside that span. The
    serial-list guard (:func:`_comma_stack_looks_like_serial_list`)
    short-circuits to ``False`` first when the sentence's shape is a
    comma-separated list with no subordinator anywhere.
    """
    if len(spans) < 3:
        return False
    interior_indices = range(1, len(spans) - 1)
    interior_word_counts = [
        len(_WORD_RE.findall(spans[i])) for i in interior_indices
    ]
    has_subordinator_anywhere = any(
        _COMMA_STACK_SUBORDINATOR_RE.search(s) for s in spans
    )
    if (
        _comma_stack_looks_like_serial_list(interior_word_counts)
        and not has_subordinator_anywhere
    ):
        return False
    for i in interior_indices:
        word_count = len(_WORD_RE.findall(spans[i]))
        if not (
            _COMMA_STACK_SPAN_MIN_WORDS <= word_count <= _COMMA_STACK_SPAN_MAX_WORDS
        ):
            continue
        opens_with_appositive = _comma_stack_starts_with_opener(spans[i])
        next_word = _comma_stack_first_word(spans[i + 1]) if i + 1 < len(spans) else ""
        followed_by_finite_verb = next_word in _COMMA_STACK_FINITE_VERBS
        if not (opens_with_appositive or followed_by_finite_verb):
            continue
        subordinator_outside = any(
            _COMMA_STACK_SUBORDINATOR_RE.search(spans[j])
            for j in range(len(spans))
            if j != i
        )
        if subordinator_outside:
            return True
    return False


def _comma_stack_fires(
    sentence: str, *, max_commas: int, min_words: int, refined_min_commas: int
) -> bool:
    """Whether ``sentence`` trips the comma-role-stacking hard OR refined tier."""
    comma_count = sentence.count(",")
    if comma_count == 0:
        return False
    word_count = len(_WORD_RE.findall(sentence))
    if comma_count >= max_commas and word_count >= min_words:
        return True
    if comma_count < refined_min_commas:
        return False
    spans = [s.strip() for s in sentence.split(",")]
    return _comma_stack_refined_signal(spans)


def _first_prose_lineno(
    scan_lines: list[str], raw_text: str
) -> Optional[int]:
    """1-based line number of the document's first prose line, or ``None``.

    "First prose line" = the first non-blank :func:`_scannable_lines`
    entry after skipping, in order:

    1. a leading YAML front-matter block (``---`` on line 1 through the
       next ``---``);
    2. ATX heading lines (``#`` … ``######``);
    3. blank scan lines (already blanked by :func:`_scannable_lines` for
       fenced code, HTML comments, and inline code spans).

    ``scan_lines`` is index-aligned with ``raw_text.splitlines()`` (both
    derive one entry per source line), so front-matter and heading
    detection reads the raw line while the blank check reads the blanked
    scan line. Returns ``None`` for an empty document, a front-matter- or
    heading-only document, or one whose entire body is excluded — in
    which case ``scope: "first-line"`` rules produce no finding. Anchors
    positional (``scope: "first-line"``) rules.
    """
    raw_lines = raw_text.splitlines()
    start = 0
    # (1) Leading YAML front-matter: a bare ``---`` on the very first
    #     line opens a block that runs to the next bare ``---``. Skip the
    #     whole block (including both fences). An unterminated block means
    #     there is no prose.
    if raw_lines and _FRONT_MATTER_FENCE_RE.match(raw_lines[0]):
        for i in range(1, len(raw_lines)):
            if _FRONT_MATTER_FENCE_RE.match(raw_lines[i]):
                start = i + 1
                break
        else:
            return None
    # (2)/(3) First non-heading, non-blank scan line.
    for i in range(start, len(scan_lines)):
        raw_line = raw_lines[i] if i < len(raw_lines) else ""
        if _HEADING_RE.match(raw_line):
            continue
        if not scan_lines[i].strip():
            continue
        return i + 1
    return None


def _sources_block_lines(raw_text: str) -> set[int]:
    """1-based line numbers inside a ``Sources`` heading section.

    Mirrors the boundary rule from
    ``anvil.skills.memo.lib.migrate``'s ``## Sources`` parser: a
    ``Sources`` section runs from the line *after* the heading to the
    next heading of **equal or higher level** (fewer or equal ``#``
    characters), or end of document. The heading line itself is not
    "inside" the section. A document with no ``Sources`` heading (or
    with the word appearing only inside a longer heading, e.g. "##
    Sources and Methods") returns an empty set — matched exactly
    against ``anvil/lib/rhetoric_lint.py``'s ``_SOURCES_HEADING_RE``.

    Used by rules declaring ``sources_block_exempt: true`` (issue
    #751) to treat the Sources block as a legitimate apparatus home
    rather than a body-prose leak.
    """
    inside: set[int] = set()
    section_depth: Optional[int] = None
    for i, raw_line in enumerate(raw_text.splitlines(), start=1):
        depth_match = _HEADING_DEPTH_RE.match(raw_line)
        if depth_match:
            depth = len(depth_match.group(1))
            if section_depth is not None and depth <= section_depth:
                section_depth = None  # a same-or-shallower heading closes it
            if _SOURCES_HEADING_RE.match(raw_line):
                section_depth = depth
                continue  # the heading line itself is not "inside"
        if section_depth is not None:
            inside.add(i)
    return inside


def _collect_disabled_lines(
    text: str, suppress_rules: Sequence[str]
) -> set[int]:
    """1-based line numbers suppressed via ``anvil-lint-disable``.

    Same contract as ``render_gate._collect_memo_disabled_lines``:
    same-line directives suppress that line; a standalone directive
    line suppresses the next non-blank, non-directive line.
    Comma-separated rule lists are honored; any token in
    ``suppress_rules`` activates the directive.
    """
    wanted = set(suppress_rules)
    disabled: set[int] = set()
    lines = text.splitlines()
    for i, line in enumerate(lines):
        for m in _LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",") if r.strip()}
            if not (rules & wanted):
                continue
            disabled.add(i + 1)
            tail = line[m.end():].strip()
            head = line[: m.start()].strip()
            if tail or head:
                # Inline directive — same-line suppression only.
                continue
            for j in range(i + 1, len(lines)):
                next_line = lines[j]
                if not next_line.strip():
                    continue
                if _LINT_DISABLE_RE.search(next_line):
                    continue
                disabled.add(j + 1)
                break
    return disabled


# Rule loading / validation -------------------------------------------------------


def _coerce_severity(value: object) -> str:
    """Coerce a declared severity to the advisory contract.

    ``"info"`` passes through; everything else — including the
    forbidden upgrade to ``"error"`` — coerces to ``"warning"``.
    """
    if isinstance(value, str) and value.strip().lower() in _VALID_SEVERITIES:
        return value.strip().lower()
    return SEVERITY_WARNING


def _validate_rule(rule: object) -> tuple[Optional[dict], Optional[str]]:
    """Normalize one rule dict. Returns ``(normalized, error)``.

    A valid rule yields ``(dict, None)``; an invalid one yields
    ``(None, "<reason>")`` for the caller to surface as a config
    finding (the broken-declaration posture: skipped, not silent).
    """
    if not isinstance(rule, dict):
        return (None, f"rule is not an object: {rule!r}")
    rule_id = rule.get("id")
    if not isinstance(rule_id, str) or not rule_id.strip():
        return (None, f"rule missing string 'id': {rule!r}")
    kind = rule.get("kind")
    if kind not in _VALID_KINDS:
        return (
            None,
            f"rule {rule_id!r}: invalid kind {kind!r} "
            f"(expected one of {', '.join(_VALID_KINDS)})",
        )
    # ``long_sentence``/``sentence_variance`` rules have no regex pattern —
    # they measure document-level sentence-length statistics, not matches —
    # so ``pattern`` is required for every other kind only.
    pattern: Optional[str] = None
    if kind not in _PATTERNLESS_KINDS:
        pattern = rule.get("pattern")
        if not isinstance(pattern, str) or not pattern:
            return (None, f"rule {rule_id!r}: missing string 'pattern'")
    normalized: dict = {
        "id": rule_id.strip(),
        "kind": kind,
        "message": rule.get("message")
        if isinstance(rule.get("message"), str)
        else f"rule {rule_id!r} matched",
        "severity": _coerce_severity(rule.get("severity")),
    }
    if pattern is not None:
        normalized["pattern"] = pattern
    if kind == RULE_KIND_LONG_SENTENCE:
        threshold = rule.get("max_per_1000_words")
        if (
            isinstance(threshold, bool)
            or not isinstance(threshold, (int, float))
            or threshold <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: long_sentence kind requires numeric "
                f"'max_per_1000_words' > 0 (got {threshold!r})",
            )
        normalized["max_per_1000_words"] = float(threshold)
        min_words = rule.get("min_words", DEFAULT_FREQUENCY_MIN_WORDS)
        if (
            isinstance(min_words, bool)
            or not isinstance(min_words, (int, float))
            or min_words < 0
        ):
            min_words = DEFAULT_FREQUENCY_MIN_WORDS
        normalized["min_words"] = int(min_words)
        sentence_word_threshold = rule.get(
            "sentence_word_threshold", DEFAULT_LONG_SENTENCE_WORD_THRESHOLD
        )
        if (
            isinstance(sentence_word_threshold, bool)
            or not isinstance(sentence_word_threshold, (int, float))
            or sentence_word_threshold <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: long_sentence kind requires numeric "
                f"'sentence_word_threshold' > 0 "
                f"(got {sentence_word_threshold!r})",
            )
        normalized["sentence_word_threshold"] = int(sentence_word_threshold)
    elif kind == RULE_KIND_SENTENCE_VARIANCE:
        min_cv = rule.get("min_cv")
        if (
            isinstance(min_cv, bool)
            or not isinstance(min_cv, (int, float))
            or min_cv <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: sentence_variance kind requires numeric "
                f"'min_cv' > 0 (got {min_cv!r})",
            )
        normalized["min_cv"] = float(min_cv)
        min_words = rule.get("min_words", DEFAULT_FREQUENCY_MIN_WORDS)
        if (
            isinstance(min_words, bool)
            or not isinstance(min_words, (int, float))
            or min_words < 0
        ):
            min_words = DEFAULT_FREQUENCY_MIN_WORDS
        normalized["min_words"] = int(min_words)
        # Sample-size floor distinct from ``min_words``: a document could
        # clear the word floor with very few sentences (e.g. one long run-on
        # sentence), and a CV computed over fewer than a handful of
        # sentences is a coin flip, not a rhythm measurement. Permissive
        # coercion (like ``min_words``) — an invalid override falls back to
        # the documented default rather than erroring the whole rule.
        min_sentences = rule.get(
            "min_sentences", DEFAULT_SENTENCE_VARIANCE_MIN_SENTENCES
        )
        if (
            isinstance(min_sentences, bool)
            or not isinstance(min_sentences, (int, float))
            or min_sentences < 2
        ):
            min_sentences = DEFAULT_SENTENCE_VARIANCE_MIN_SENTENCES
        normalized["min_sentences"] = int(min_sentences)
    elif kind == RULE_KIND_COMMA_STACK:
        max_commas = rule.get("max_commas", DEFAULT_COMMA_STACK_MAX_COMMAS)
        if (
            isinstance(max_commas, bool)
            or not isinstance(max_commas, (int, float))
            or max_commas <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: comma_stack kind requires numeric "
                f"'max_commas' > 0 (got {max_commas!r})",
            )
        normalized["max_commas"] = int(max_commas)
        # NOTE: a per-sentence word floor for the hard tier, NOT the
        # document-level ``min_words`` floor used by
        # frequency/long_sentence/sentence_variance — see the module
        # docstring's ``comma_stack`` bullet.
        min_words = rule.get("min_words", DEFAULT_COMMA_STACK_MIN_WORDS)
        if (
            isinstance(min_words, bool)
            or not isinstance(min_words, (int, float))
            or min_words <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: comma_stack kind requires numeric "
                f"'min_words' > 0 (got {min_words!r})",
            )
        normalized["min_words"] = int(min_words)
        refined_min_commas = rule.get(
            "refined_min_commas", DEFAULT_COMMA_STACK_REFINED_MIN_COMMAS
        )
        if (
            isinstance(refined_min_commas, bool)
            or not isinstance(refined_min_commas, (int, float))
            or refined_min_commas <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: comma_stack kind requires numeric "
                f"'refined_min_commas' > 0 "
                f"(got {refined_min_commas!r})",
            )
        normalized["refined_min_commas"] = int(refined_min_commas)
    elif kind == RULE_KIND_FREQUENCY:
        threshold = rule.get("max_per_1000_words")
        if (
            isinstance(threshold, bool)
            or not isinstance(threshold, (int, float))
            or threshold <= 0
        ):
            return (
                None,
                f"rule {rule_id!r}: frequency kind requires numeric "
                f"'max_per_1000_words' > 0 (got {threshold!r})",
            )
        normalized["max_per_1000_words"] = float(threshold)
        min_words = rule.get("min_words", DEFAULT_FREQUENCY_MIN_WORDS)
        if (
            isinstance(min_words, bool)
            or not isinstance(min_words, (int, float))
            or min_words < 0
        ):
            min_words = DEFAULT_FREQUENCY_MIN_WORDS
        normalized["min_words"] = int(min_words)
        # Frequency patterns are counted as regex matches (``findall``),
        # so a rule can count spans like ``\*\*[^*]+\*\*`` (bold), not
        # only single literal tokens. A single-char literal such as the
        # em-dash ``—`` counts identically under either model. Compile
        # now so a malformed pattern is a config finding, not a
        # mid-scan crash.
        try:
            normalized["_compiled"] = _compile_rule_pattern(kind, pattern)
        except re.error as exc:
            return (None, f"rule {rule_id!r}: invalid regex pattern: {exc}")
        # Optional human label used only in the frequency finding's
        # diagnostic tail (so an opaque regex like the bold-span pattern
        # reads as "bold span" instead of the raw source).
        label = rule.get("label")
        if isinstance(label, str) and label.strip():
            normalized["label"] = label.strip()
    else:
        # Positional scope (phrase/regex only; frequency is always
        # document-level and never receives a ``scope`` key). Unknown or
        # absent values coerce to ``"body"`` — the original behavior.
        scope_raw = rule.get("scope", "body")
        normalized["scope"] = "first-line" if scope_raw == "first-line" else "body"
        # Sources-block exemption (issue #751): opt-in bool, defaults
        # False. Any non-``True`` value (missing key, non-bool) coerces
        # to False rather than erroring — this is a permissive modifier,
        # not a validated enum like ``scope``.
        normalized["sources_block_exempt"] = rule.get("sources_block_exempt") is True
        # Compile now so a malformed regex is a config finding, not a
        # mid-scan crash.
        try:
            normalized["_compiled"] = _compile_rule_pattern(kind, pattern)
        except re.error as exc:
            return (None, f"rule {rule_id!r}: invalid regex pattern: {exc}")
    return (normalized, None)


def _compile_rule_pattern(kind: str, pattern: str) -> re.Pattern:
    """Compile a phrase/regex rule pattern (always case-insensitive)."""
    if kind == RULE_KIND_PHRASE:
        escaped = re.escape(pattern)
        # Straight apostrophe in a phrase also matches the typographic
        # apostrophe (memo prose is usually smart-quoted).
        escaped = escaped.replace("'", "['’]")
        return re.compile(r"\b" + escaped + r"\b", re.IGNORECASE)
    return re.compile(pattern, re.IGNORECASE)


def _load_rule_source(
    source: object, *, origin: str
) -> tuple[list[dict], set[str], list[RhetoricFinding]]:
    """Normalize one consumer rule source (parsed dict or rule list).

    Returns ``(valid_rules, disable_ids, config_findings)``. A source
    may be either the documented file shape (``{"name", "rules",
    "disable"}``) or a bare list of rule dicts.
    """
    findings: list[RhetoricFinding] = []
    if isinstance(source, list):
        rules_raw: list = source
        disable_raw: list = []
    elif isinstance(source, dict):
        rules_raw = source.get("rules", [])
        disable_raw = source.get("disable", [])
        if not isinstance(rules_raw, list):
            findings.append(
                RhetoricFinding(
                    rule_id=CONFIG_RULE_ID,
                    severity=SEVERITY_WARNING,
                    message=(
                        f"{origin}: 'rules' is not a list; consumer rules "
                        "ignored (framework defaults still apply)."
                    ),
                )
            )
            rules_raw = []
        if not isinstance(disable_raw, list):
            findings.append(
                RhetoricFinding(
                    rule_id=CONFIG_RULE_ID,
                    severity=SEVERITY_WARNING,
                    message=(
                        f"{origin}: 'disable' is not a list; ignored."
                    ),
                )
            )
            disable_raw = []
    else:
        findings.append(
            RhetoricFinding(
                rule_id=CONFIG_RULE_ID,
                severity=SEVERITY_WARNING,
                message=(
                    f"{origin}: expected an object with 'rules'/'disable' "
                    f"or a list of rules, got {type(source).__name__}; "
                    "consumer rules ignored (framework defaults still apply)."
                ),
            )
        )
        return ([], set(), findings)

    valid: list[dict] = []
    for raw in rules_raw:
        normalized, error = _validate_rule(raw)
        if normalized is not None:
            valid.append(normalized)
        else:
            findings.append(
                RhetoricFinding(
                    rule_id=CONFIG_RULE_ID,
                    severity=SEVERITY_WARNING,
                    message=f"{origin}: skipped invalid rule — {error}",
                )
            )
    disable = {d.strip() for d in disable_raw if isinstance(d, str) and d.strip()}
    return (valid, disable, findings)


def _resolve_rules(
    extra_rules: Optional[object],
    extra_rules_path: Optional[Union[str, Path]],
) -> tuple[list[dict], list[RhetoricFinding]]:
    """Merge defaults + in-memory extras + consumer rule file.

    Merge order: framework defaults → ``extra_rules`` →
    ``extra_rules_path``. Later sources win on id collision; ``disable``
    ids (from any source) remove rules from the merged set. Returns
    ``(effective_rules, config_findings)``.
    """
    findings: list[RhetoricFinding] = []
    merged: dict[str, dict] = {}
    disabled_ids: set[str] = set()

    # Defaults are trusted but run through the same validator so the
    # in-module set can never drift from the documented schema.
    for raw in DEFAULT_RHETORIC_RULES:
        normalized, error = _validate_rule(raw)
        if normalized is not None:
            merged[normalized["id"]] = normalized
        else:  # pragma: no cover — defaults are validated by tests
            findings.append(
                RhetoricFinding(
                    rule_id=CONFIG_RULE_ID,
                    severity=SEVERITY_WARNING,
                    message=f"default rule set: {error}",
                )
            )

    if extra_rules is not None:
        rules, disable, src_findings = _load_rule_source(
            extra_rules, origin="extra_rules"
        )
        findings.extend(src_findings)
        for rule in rules:
            merged[rule["id"]] = rule
        disabled_ids |= disable

    if extra_rules_path is not None:
        path = Path(extra_rules_path)
        origin = str(path)
        try:
            parsed = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            # Graceful-degrade: defaults-only run + ONE warning finding
            # naming the parse error (customer_context.py posture).
            findings.append(
                RhetoricFinding(
                    rule_id=CONFIG_RULE_ID,
                    severity=SEVERITY_WARNING,
                    message=(
                        f"{origin}: could not load consumer rhetoric rules "
                        f"({exc}); framework defaults still apply."
                    ),
                )
            )
        else:
            rules, disable, src_findings = _load_rule_source(
                parsed, origin=origin
            )
            findings.extend(src_findings)
            for rule in rules:
                merged[rule["id"]] = rule
            disabled_ids |= disable

    effective = [r for rid, r in merged.items() if rid not in disabled_ids]
    return (effective, findings)


# Public API ----------------------------------------------------------------------


def scannable_lines(text: str) -> list[str]:
    """Public entry point for the fenced-code / HTML-comment / inline-code
    exclusion mask (issue #922).

    Thin public wrapper around :func:`_scannable_lines`, whose docstring
    documents the exact exclusion contract (fenced code blocks blanked
    wholesale, HTML comments stripped including multi-line spans, inline
    code spans removed — one output line per input line, so line numbers
    stay anchored to the original source). Exists so a second consumer can
    reuse the identical exclusion scope without re-implementing it or
    reaching into a leading-underscore internal: `anvil:deslop`'s
    deterministic no-fabrication gate
    (`anvil/skills/deslop/lib/no_fabrication.py`) diffs iteration N against
    N+1 over this same masked text so a fenced code sample pasted into
    ingested prose can never register as an "introduced" numeral / proper
    noun / citation token. Byte-identical output to
    :func:`_scannable_lines` — this function does no additional work.
    """
    return _scannable_lines(text)


def lint_rhetoric(
    text: str,
    *,
    extra_rules: Optional[object] = None,
    extra_rules_path: Optional[Union[str, Path]] = None,
    suppress_rules: Sequence[str] = DEFAULT_SUPPRESS_RULES,
) -> RhetoricLintResult:
    """Run the deterministic rhetoric lint over ``text``.

    Parameters
    ----------
    text:
        Body markdown to scan. Fenced code blocks, HTML comments, and
        inline code spans are excluded (code samples must not fire;
        the suppression directive must not self-match).
    extra_rules:
        Optional in-memory consumer rules: either a bare list of rule
        dicts or the documented file shape (``{"name", "rules",
        "disable"}``). Merged over the defaults (id collision →
        consumer wins).
    extra_rules_path:
        Optional path to a consumer JSON rule file (same shape).
        Malformed input graceful-degrades to a defaults-only run with
        one warning finding naming the parse error. This is the
        integration point for the #461 voice contract's
        ``voice.rhetoric_rules`` sub-key, wired in issue #468:
        ``anvil.lib.project_brief.resolve_rhetoric_rules`` resolves
        the declared path and memo-render step 4g forwards it through
        ``render_gate.gate(kind="memo", rhetoric_rules_path=...)``
        (a missing declared file is forwarded too, so the OSError
        graceful-degrade above surfaces the broken declaration).
    suppress_rules:
        Directive tokens honored for per-line suppression. Defaults to
        :data:`DEFAULT_SUPPRESS_RULES` (the memo gate dimension name
        plus the generic ``rhetoric_lint`` token).

    Returns
    -------
    RhetoricLintResult
        ``findings`` (warning/info only — never error), ``words``
        (the per-1000-words denominator over the scanned text), and
        ``rules_applied`` (effective rule ids after merge/disable).
    """
    rules, findings = _resolve_rules(extra_rules, extra_rules_path)
    scan_lines = _scannable_lines(text)
    scan_lines = _collapse_markdown_links(scan_lines)
    disabled_lines = _collect_disabled_lines(text, suppress_rules)
    words = sum(len(_WORD_RE.findall(line)) for line in scan_lines)
    # Computed once for all positional (``scope: "first-line"``) rules.
    first_prose_lineno = _first_prose_lineno(scan_lines, text)
    # Computed lazily (only if a ``long_sentence``, ``sentence_variance``,
    # or ``comma_stack`` rule is active) and cached across all three
    # kinds — the tokenization does not depend on any per-rule setting.
    # ``sentence_word_counts`` derives from ``sentence_chunks`` (see
    # :func:`_sentence_word_counts`), so caching the chunks once lets
    # ``comma_stack`` (which needs the text, not just the counts) reuse
    # the same split without re-running it.
    sentence_chunks: Optional[list[str]] = None
    sentence_word_counts: Optional[list[int]] = None
    # Computed once for all ``sources_block_exempt`` rules (issue #751).
    sources_lines = _sources_block_lines(text)

    for rule in rules:
        if rule["kind"] == RULE_KIND_LONG_SENTENCE:
            if words < rule["min_words"] or words == 0:
                continue
            if sentence_chunks is None:
                sentence_chunks = _sentence_chunks(scan_lines)
            if sentence_word_counts is None:
                sentence_word_counts = [
                    len(_WORD_RE.findall(c)) for c in sentence_chunks
                ]
            threshold = rule["sentence_word_threshold"]
            count = sum(1 for wc in sentence_word_counts if wc > threshold)
            density = count / words * 1000.0
            if density > rule["max_per_1000_words"]:
                findings.append(
                    RhetoricFinding(
                        rule_id=rule["id"],
                        severity=rule["severity"],
                        message=(
                            f"{rule['message']} "
                            f"({count} sentence(s) over {threshold} words "
                            f"in {words} words = {density:.1f}/1000; "
                            f"threshold {rule['max_per_1000_words']:g}/1000)."
                        ),
                        line=None,
                        match=None,
                    )
                )
            continue
        if rule["kind"] == RULE_KIND_SENTENCE_VARIANCE:
            if words < rule["min_words"] or words == 0:
                continue
            if sentence_chunks is None:
                sentence_chunks = _sentence_chunks(scan_lines)
            if sentence_word_counts is None:
                sentence_word_counts = [
                    len(_WORD_RE.findall(c)) for c in sentence_chunks
                ]
            # Zero-word "sentences" (e.g. a stray "..." run) are not a
            # length observation; excluding them keeps the statistic about
            # actual sentence rhythm, not tokenization artifacts.
            counts = [wc for wc in sentence_word_counts if wc > 0]
            if len(counts) < rule["min_sentences"]:
                continue
            mean = statistics.mean(counts)
            if mean <= 0:
                continue
            cv = statistics.pstdev(counts) / mean
            if cv < rule["min_cv"]:
                findings.append(
                    RhetoricFinding(
                        rule_id=rule["id"],
                        severity=rule["severity"],
                        message=(
                            f"{rule['message']} "
                            f"(coefficient of variation {cv:.2f} across "
                            f"{len(counts)} sentence(s), mean {mean:.1f} "
                            f"words; floor {rule['min_cv']:g})."
                        ),
                        line=None,
                        match=None,
                    )
                )
            continue
        if rule["kind"] == RULE_KIND_COMMA_STACK:
            if sentence_chunks is None:
                sentence_chunks = _sentence_chunks(scan_lines)
            for sentence in sentence_chunks:
                if not _comma_stack_fires(
                    sentence,
                    max_commas=rule["max_commas"],
                    min_words=rule["min_words"],
                    refined_min_commas=rule["refined_min_commas"],
                ):
                    continue
                comma_count = sentence.count(",")
                excerpt = sentence if len(sentence) <= 120 else sentence[:117] + "..."
                findings.append(
                    RhetoricFinding(
                        rule_id=rule["id"],
                        severity=rule["severity"],
                        message=f"{comma_count} {rule['message']}",
                        line=None,
                        match=excerpt,
                    )
                )
            continue
        if rule["kind"] == RULE_KIND_FREQUENCY:
            freq_regex = rule["_compiled"]
            count = sum(len(freq_regex.findall(line)) for line in scan_lines)
            if words < rule["min_words"] or words == 0:
                continue
            density = count / words * 1000.0
            if density > rule["max_per_1000_words"]:
                label = rule.get("label") or rule["pattern"]
                findings.append(
                    RhetoricFinding(
                        rule_id=rule["id"],
                        severity=rule["severity"],
                        message=(
                            f"{rule['message']} "
                            f"({count} occurrence(s) of {label!r} "
                            f"in {words} words = {density:.1f}/1000; "
                            f"threshold {rule['max_per_1000_words']:g}/1000)."
                        ),
                        line=None,
                        match=rule["pattern"],
                    )
                )
            continue
        regex = rule["_compiled"]
        rule_scope = rule.get("scope", "body")
        rule_sources_exempt = rule.get("sources_block_exempt", False)
        for lineno, line in enumerate(scan_lines, start=1):
            # Positional rules evaluate only the first prose line; when
            # there is none (empty / all-excluded doc), they never fire.
            if rule_scope == "first-line" and lineno != first_prose_lineno:
                continue
            # Sources-block exemption (issue #751): the block is the
            # tag's documented home, not a leak — skip entirely (no
            # finding at all, not even suppressed-info).
            if rule_sources_exempt and lineno in sources_lines:
                continue
            for m in regex.finditer(line):
                if lineno in disabled_lines:
                    findings.append(
                        RhetoricFinding(
                            rule_id=rule["id"],
                            severity=SEVERITY_INFO,
                            message=f"{rule['message']} (suppressed)",
                            line=lineno,
                            match=m.group(0),
                        )
                    )
                else:
                    findings.append(
                        RhetoricFinding(
                            rule_id=rule["id"],
                            severity=rule["severity"],
                            message=rule["message"],
                            line=lineno,
                            match=m.group(0),
                        )
                    )

    return RhetoricLintResult(
        findings=findings,
        words=words,
        rules_applied=sorted(r["id"] for r in rules),
    )


__all__ = [
    "CONFIG_RULE_ID",
    "DEFAULT_COMMA_STACK_MAX_COMMAS",
    "DEFAULT_COMMA_STACK_MIN_WORDS",
    "DEFAULT_COMMA_STACK_REFINED_MIN_COMMAS",
    "DEFAULT_FREQUENCY_MIN_WORDS",
    "DEFAULT_LONG_SENTENCE_WORD_THRESHOLD",
    "DEFAULT_RHETORIC_RULES",
    "DEFAULT_SENTENCE_VARIANCE_MIN_CV",
    "DEFAULT_SENTENCE_VARIANCE_MIN_SENTENCES",
    "DEFAULT_SUPPRESS_RULES",
    "EMDASH_MAX_PER_1000_WORDS",
    "EMPHASIS_MAX_PER_1000_WORDS",
    "LONG_SENTENCE_MAX_PER_1000_WORDS",
    "RULE_KIND_COMMA_STACK",
    "RULE_KIND_FREQUENCY",
    "RULE_KIND_LONG_SENTENCE",
    "RULE_KIND_PHRASE",
    "RULE_KIND_REGEX",
    "RULE_KIND_SENTENCE_VARIANCE",
    "RhetoricFinding",
    "RhetoricLintResult",
    "SEVERITY_INFO",
    "SEVERITY_WARNING",
    "lint_rhetoric",
    "scannable_lines",
]
