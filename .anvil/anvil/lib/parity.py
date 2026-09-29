"""Pre-flight lint: shared hard claims between sibling ``deck.md`` and ``memo.md``.

Detects **deck↔memo parity drift** — a load-bearing hard claim that lives in
one artifact but not its sibling. The classic failure mode is a memo revision
that pulls ahead of the deck (or vice versa) on a number / date / acronym
that both artifacts are supposed to share. Each pipeline (`anvil:memo`,
`anvil:deck`) advances on its own cadence under its own critic, so without
this check there is no point in the lifecycle where a shared hard-claim
universe is reconciled — the canary failure mode that surfaced this module.

This module is the **shared library promotion** of the two near-byte-identical
skill-local mirrors that shipped first:

- ``anvil/skills/deck/lib/parity_lint.py`` (PR #205, first consumer, issue #200)
- ``anvil/skills/memo/lib/parity_lint.py`` (PR #215, second consumer)

Per CLAUDE.md §"Skill-local first, lib promotion later" — "wait for the second
consumer before generalizing." The second-consumer trigger fired on PR #215's
merge and this promotion (issue #317) is the canonical one-line import-path
swap that the two skill-local docstrings already named as the target.

Canary friction (issue #200, mirrored by issue #215)
----------------------------------------------------
Studio canary, 2026-06-01 portfolio review/revise pass: Citation Clear was
the first studio venture with both memo and deck pipelines shipped
(memo.3 + deck.3 at 35/40 advance:TRUE). During the revise pass, the
reviser introduced a load-bearing insurer benchmark — "~50–60% completion"
— into memo.4 that deck.3 lacked. **No anvil primitive detected this
drift.** Shared hard claims (FTC $193K / 5-0 / Jan 2025, NYC FY24 26.6%,
SFMTA $126M+ since April 2024, pricing $8.99/$29.99, kill thresholds)
silently drift across independent revision cycles. The studio cohort now
has ~10 threads on both `anvil:memo` and `anvil:deck` — every one is a
future drift surface.

The reference implementation pattern (``Finding`` / ``LintResult`` /
``_LINT_DISABLE_RE`` / ``lint_source`` / ``lint_<artifact>``) descends from
``anvil/skills/deck/lib/marp_lint.py`` and the parallel
``anvil/skills/memo/lib/memo_image_refs.py``. The shared-lib promotion
preserves the per-side wrapper contract (``lint_deck_memo_parity`` /
``lint_memo_deck_parity``) and the per-side rule name
(``deck_memo_parity`` / ``memo_deck_parity``) so the two ``*-review.md``
command files remain byte-identical pre- and post-promotion.

Second-consumer trigger fired on merge of #215
----------------------------------------------
Per CLAUDE.md §"Skill-local first, lib promotion later" — "wait for the second
consumer before generalizing." With both ``anvil/skills/deck/lib/parity_lint.py``
(PR #205, first consumer) and ``anvil/skills/memo/lib/parity_lint.py`` (PR
#215, second consumer) on disk, the trigger condition was satisfied for the
first time. This module is the resulting promotion; both skill-local modules
are now thin re-exports.

Load-bearingness filter (issue #553)
------------------------------------
v0 of this lint fired one undifferentiated "drift" warning per ``only_in_memo``
token. The canary failure mode that surfaced this issue (Docent, 2026-06-12)
was that thin-deck-vs-rich-memo is the **expected** steady state — decks are
legitimately terser than memos. The operator (correctly) treated all 38
``only_in_memo`` warnings on Docent as the "accept the divergence" branch and
bulk-dismissed them. A **load-bearing economic drop** (a ``$/seat``
contribution-margin number with no deck-side counterpart) hid in that noise.

The fix is **not** a new direction — both directions already emit. It is a
**load-bearingness filter** layered over the existing ``only_in_memo`` set
that promotes the load-bearing-economic subset to a new sharper warning class
(``side="only_in_memo_economic"``) the reviser consults before deciding to
bulk-dismiss.

**Schema choice (Option A from the issue #553 curator brief)**: ``side`` is
extended to the Literal value ``"only_in_memo_economic"`` and ``LintResult``
exposes the promoted subset via a new ``only_in_memo_economic`` property
paralleling ``only_in_memo`` / ``only_in_deck``. **Invariants**:

- ``only_in_memo`` is **unchanged** — it still carries the full set of tokens
  present in memo but absent from deck. The promoted subset is **additive**
  surfacing; legacy consumers reading ``only_in_memo`` see byte-identical
  behavior.
- ``set(only_in_memo_economic) ⊆ set(only_in_memo)``. A token promoted to the
  economic subset is also recorded as an ``only_in_memo`` finding (under a
  separate ``Finding`` with ``side="only_in_memo"``) so the full set is
  observable without traversing the economic subset.
- The classifier respects the existing ``<!-- anvil-lint-disable:
  <rule> -->`` escape hatch — a suppressed token is downgraded to ``info``
  on **both** the ``only_in_memo`` and the ``only_in_memo_economic`` findings;
  no second escape mechanism.
- Phase A severity preserved: promoted findings ship at ``severity="warning"``
  (or ``"info"`` if suppressed). They do NOT promote to ``"error"``.

**Heuristic** (deliberately conservative — false-negative-tolerant):

- A token is *load-bearing-economic* if (a) its extractor rule label is
  ``money``, ``percent``, or ``unit_int`` AND (b) the memo source line
  carrying the token co-occurs (same line, or within ±3 lines) with one of
  :data:`ECONOMIC_CONTEXT_VOCABULARY` (attach / ARPU / ACV / ARR / MRR / LTV
  / CAC / margin / payback / kill threshold / unit economics / take rate /
  rev share / pricing / conversion / churn / retention / GMV / TAM / SAM /
  SOM).
- Bare acronym tokens (e.g., ``FTC``, ``SFMTA``) are **NOT** promoted —
  acronyms appearing in regulatory-background prose remain undifferentiated
  ``only_in_memo`` noise. The narrow "money / percent / unit_int near
  economic-context vocab" cut is the v0 calibration; vocabulary drift is
  expected as the canary surfaces real false positives.

**Phase A non-gating** preserved: economic-subset findings ship at warning
severity, do NOT contribute to ``lint_critical_flag``, and do NOT force
``advance: false``. The reviser side (``deck-revise``) is responsible for
treating the promoted subset with sharper framing ("memo carried this
substance; the deck dropped it — was that deliberate?") instead of the bulk
"drift, reconcile" framing the v0 ``only_in_memo`` warnings carry.

Quarantine corpus — BRIEF-mandated omissions (issue #914)
-----------------------------------------------------------
The load-bearingness filter above models memo↔deck divergence as
*accidental* — every promoted ``only_in_memo_economic`` token is framed as
a "should you port this?" decision. That framing is WRONG for a token a
project's ``BRIEF.md`` has deliberately quarantined: a superseded or
unverified figure (canary: a memo's ``$400M`` gross-revenue figure when
the project's hard rule requires the ``$256M`` net figure instead; an
unverified ``20-40%`` preferred-vs-standard spread) that is **correctly**
absent from the deck, not accidentally dropped. Pre-#914, the lint's
sharpest channel — the economic promotion — was recommending exactly the
hard-rule violation the BRIEF forbids.

``ProjectBrief.quarantine`` (``anvil/lib/project_brief.py``) is the fix: a
project author lists the literal tokens a hard rule forbids porting
(``quarantine: ["$400M", "20-40%"]``), separate from the free-form
``hard_rules`` prose. ``lint_source()`` accepts the resulting token set as
``quarantine_corpus: frozenset[str]``; the two file wrappers
(``lint_deck_memo_parity`` / ``lint_memo_deck_parity``) load it
automatically via :func:`_extract_quarantine_corpus` against the sibling
``BRIEF.md`` at the project root (the thread root's parent, same
discovery convention as ``load_rubric_overrides_for_slug``).

**Two distinct effects, both additive**:

- A quarantined token found in the memo (and therefore in ``only_in_memo``)
  is **excluded from ``only_in_memo_economic`` promotion** and instead
  gets its own ``side="only_in_memo_quarantined"`` finding layered on top
  of the underlying ``only_in_memo`` finding (same additive-surfacing
  shape as the economic promotion) — "correctly absent per BRIEF hard
  rule — do not port," not a divergence awaiting a decision.
- A quarantined token found **anywhere in the deck body** (whether or not
  it is also memo-side) raises a NEW ``side="quarantine_violation"``
  finding — a real hard-rule violation this lint did not previously
  detect at all.

An empty ``quarantine_corpus`` (the default, and every consumer that
predates issue #914 or has no ``quarantine:`` key on its BRIEF) is a true
no-op — byte-identical to pre-#914 behavior.

**Derived-forms caveat (explicitly out of scope for this pass)**: the
quarantine corpus matches **literal tokens only**. A quarantined
percentage that reappears in the deck (or is absent-but-implied in the
memo) as its arithmetic derivation — e.g. a quarantined ``20-40%`` rate
surfacing as a derived ``$360-720/yr`` dollar range one division away —
is NOT detected. This is a known gap, not an oversight: full derivation
detection is a follow-on tracked against canary signal (see issue #914).
A reviser porting content near a quarantined figure MUST manually check
for derived forms; the lint only catches the literal figure.

Phase A / Phase B (warning vs. error severity)
----------------------------------------------
v0 ships at **`warning` severity** for every parity finding. The lint is
*observational* on first ship: it surfaces drift in `findings.md` and the
operator's next-step list, but does NOT contribute to the
``lint_critical_flag`` and does NOT force ``advance: false``. The
``deck-review`` verdict aggregation (step 12) and ``memo-review`` verdict
aggregation (step 7) are byte-identical to a thread without the parity lint
enabled.

Phase B promotion to ``error`` (and therefore ``advance: false``-gating)
is a separate decision deferred 2–4 weeks after Phase A merge, based on
canary consumption signal — does the warning fire reliably on actionable
drift, or is the false-positive volume too high? This Phase A / Phase B
ship-with-falsifiability pattern (single named consumer + bounded
observation window + explicit kill-switch criterion) is the framework's
established negative-result discipline; see ``WORK_LOG.md`` 2026-06-02
(issue #227) for the canonical kill-switch precedent — a Phase A
primitive that did not survive its bounded canary window and was cleanly
retracted. The pattern itself — ship-with-falsifiability, observe,
retract-cleanly — is what carries forward here.

What the lint does (v0)
-----------------------

Both wrappers (``lint_deck_memo_parity`` and ``lint_memo_deck_parity``)
share the same core:

1. **Graceful-skip when no sibling.** If the sibling version dir is
   ``None`` or the sibling body is missing, returns
   ``LintResult(skipped=True, reason="...")`` with no findings. The
   single-pipeline case (most non-Studio consumers, and Studio threads
   where only one pipeline has shipped) is the common path; the lint is
   intentionally inert there. The host review proceeds normally.
2. **Hard-claim extraction.** Apply a small set of conservative regex
   extractors over both bodies (see :data:`EXTRACTORS`):

   - **Money**: ``$XXK/M/B``, decimal prices (``$8.99``, ``$29.99``).
   - **Percentages**: ``26.6%``, ``50–60%`` (en-dash range), ``50-60%``
     (ascii range).
   - **Dates / quarters / FY**: ``Q1 FY24``, ``FY2024``, ``20XX``.
   - **Named months + year**: ``Jan 2025``, ``April 2024``.
   - **ALL-CAPS acronyms** (length 2–6): ``FTC``, ``SFMTA``, ``NYC``,
     ``LOI``. Conservative bound (length 2–6) deliberately rejects prose
     ALL-CAPS (``WHO``, ``DO NOT``, etc.) and over-long token strings.
   - **Unit-bearing integers**: ``8 pilots``, ``50 LOIs``, ``250k
     plants``. The unit vocabulary is small and conservative (see
     :data:`UNIT_VOCABULARY`).

   Each match is captured as a ``(token, line_number)`` pair so the
   diagnostic is grounded.
3. **Set comparison.** Two sets of tokens — one per artifact body —
   are compared by **exact-string equality**. Semantic equivalence
   (``$193K`` vs ``$193,000`` vs ``193 thousand``) is **explicitly
   deferred** to a follow-on issue. v0 surfaces ``only_in_memo`` and
   ``only_in_deck`` lists.
4. **Findings.** One ``Finding`` per token in ``only_in_memo`` or
   ``only_in_deck`` at ``severity="warning"`` (v0 contract). The
   ``Finding.side`` values (``"only_in_memo"`` / ``"only_in_deck"``) are
   preserved verbatim across both wrappers — they describe *which body
   the token came from*, independent of which side is "primary".
5. **Escape hatch.** ``<!-- anvil-lint-disable: <rule> -->`` on the
   line of (or immediately above) a deliberately-one-sided claim
   **downgrades that finding to ``info``**. The mechanism mirrors
   ``marp_lint`` and ``memo_image_refs`` exactly.

What v0 explicitly defers (remains queued against this lib module)
------------------------------------------------------------------

- **Semantic-equivalence matching** (``$193K`` ↔ ``$193,000``): follow-on
  if the canary surfaces high false-positive volume.
- **Promotion to ``error`` severity** (Phase B): follow-on after 2–4 weeks
  of canary consumption signal.
- **Standalone ``/anvil:parity-check <thread>`` command**: not in v0; the
  ``deck-review`` step 5d / ``memo-review`` step 4d invocations are the
  carriers.
- **Centralizing sibling-version discovery inside the wrapper**: still
  caller's responsibility in v0 (mirrors the pre-promotion contract).

Public API
----------
``lint_source(deck_source, memo_source, *, rule="deck_memo_parity", figure_corpus=frozenset(), quarantine_corpus=frozenset()) -> LintResult``
    Generic core that operates on two in-memory strings. The default
    ``rule`` preserves deck-side semantics so the existing deck-side
    ``lint_source(deck_source, memo_source)`` call is byte-compatible.
    Memo-side wrapper passes ``rule="memo_deck_parity"``.
    ``quarantine_corpus`` (issue #914) is an optional set of literal
    BRIEF-quarantined tokens; see "Quarantine corpus" above.
``lint_deck_memo_parity(deck_version_dir, memo_version_dir) -> LintResult``
    Deck-side file wrapper. Discovers the source files inside the
    version dirs, auto-loads the sibling project ``BRIEF.md``'s
    quarantine corpus, and handles the graceful-skip path.
``lint_memo_deck_parity(memo_version_dir, deck_version_dir) -> LintResult``
    Memo-side file wrapper. Symmetric to ``lint_deck_memo_parity`` with
    primary/sibling roles swapped (including quarantine-corpus loading).
``lint_parity(primary_path, sibling_path, primary_kind, sibling_kind) -> LintResult``
    Unified wrapper dispatching to the deck-side or memo-side primary-
    artifact framing based on ``primary_kind``. Centralizes the
    sibling-pair surface that future versions can grow into.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal


# Module-level metadata --------------------------------------------------------

#: Deck-side rule label. Single rule in v0; mirrors ``marp_lint.PORTED_RULES``
#: shape so any future addition is a tuple append.
RULES_DECK: tuple[str, ...] = ("deck_memo_parity",)

#: Memo-side rule label. Single rule in v0; symmetric mirror of
#: ``RULES_DECK``.
RULES_MEMO: tuple[str, ...] = ("memo_deck_parity",)


# Anvil lint suppression directive. Mirrors ``marp_lint._LINT_DISABLE_RE``
# and ``memo_image_refs._LINT_DISABLE_RE`` exactly so a comma-separated
# rule list (``<!-- anvil-lint-disable: deck_memo_parity, some-other -->``)
# is honored across all skill-local lints.
_LINT_DISABLE_RE = re.compile(
    r"<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->",
)


# Result types -----------------------------------------------------------------


@dataclass
class Finding:
    """A single parity-lint hit.

    Field shape mirrors ``marp_lint.Finding`` so a consumer that already
    handles deck findings can handle parity findings without a schema
    fork. ``slide`` is absent here — parity operates on a deck-memo body
    pair, not a single Marp slide list — but ``line``, ``rule``,
    ``severity``, and ``message`` are preserved. Two additional fields
    capture the parity-specific shape:

    - ``token``: the exact extracted token that diverged between the two
      bodies (e.g., ``"~50–60% completion"`` minus the leading qualifier,
      or ``"50–60%"`` from the percentage extractor).
    - ``side``: ``"only_in_memo"``, ``"only_in_deck"``,
      ``"only_in_memo_economic"``, ``"only_in_memo_quarantined"``, or
      ``"quarantine_violation"`` — which body contained the token that
      the other did not, OR (the third value) a memo-only token that the
      load-bearingness classifier promoted to the economic subset per
      issue #553, OR (the fourth value) a memo-only token that a project
      BRIEF's ``quarantine:`` list marks as deliberately not-ported per
      issue #914, OR (the fifth value) a BRIEF-quarantined token that
      appears in the deck body — a hard-rule violation, also issue #914.
      **Values preserved verbatim across both wrappers** — they describe
      *which body the token came from*, independent of which side is
      "primary". The ``"only_in_memo_economic"`` and
      ``"only_in_memo_quarantined"`` findings are **always emitted
      alongside** an ``"only_in_memo"`` finding for the same token
      (additive sharper signal, not a replacement); the two are mutually
      exclusive per token (a quarantined token is never ALSO promoted to
      ``"only_in_memo_economic"`` — see the module docstring's
      "Quarantine corpus" section). ``"quarantine_violation"`` has no
      required companion finding — it fires independently of whether the
      same token is also ``only_in_deck`` or shared with the memo.
    """

    line: int
    rule: str
    severity: str  # "warning" | "info"  (v0 ships warning-only; info is the suppressed path)
    message: str
    token: str
    side: str  # "only_in_memo" | "only_in_deck" | "only_in_memo_economic" | "only_in_memo_quarantined" | "quarantine_violation"

    def to_dict(self) -> dict:
        return {
            "line": self.line,
            "rule": self.rule,
            "severity": self.severity,
            "message": self.message,
            "token": self.token,
            "side": self.side,
        }


@dataclass
class LintResult:
    """Aggregate parity-lint result.

    The ``skipped`` / ``reason`` / ``memo_sibling`` / ``deck_sibling``
    fields support the graceful-skip path: when the lint cannot run (no
    sibling discoverable), the result still serializes a structured
    ``_summary.md`` block so the operator sees WHY the check did not
    fire.

    **Both ``memo_sibling`` and ``deck_sibling`` exist on every result**
    so neither skill's ``to_summary()`` shape breaks. The deck-side
    wrapper sets ``memo_sibling`` (and ``to_summary()`` carries it
    forward); the memo-side wrapper sets ``deck_sibling`` (and
    ``to_summary()`` carries it forward). Tests on both sides pin the
    presence of their respective field; the unused field defaults to
    ``None``.
    """

    warnings: list[Finding] = field(default_factory=list)
    infos: list[Finding] = field(default_factory=list)
    skipped: bool = False
    reason: str | None = None
    memo_sibling: str | None = None  # absolute path to memo version dir (set by deck-side wrapper)
    deck_sibling: str | None = None  # absolute path to deck version dir (set by memo-side wrapper)

    # v0 never emits errors — the lint is observational only. The field
    # is kept on the result for shape-parity with ``marp_lint.LintResult``
    # (so a future Phase B promotion to ``error`` severity does not need
    # to change the schema) but is always empty in v0.
    errors: list[Finding] = field(default_factory=list)

    @property
    def total(self) -> int:
        return len(self.errors) + len(self.warnings) + len(self.infos)

    @property
    def only_in_memo(self) -> list[str]:
        """Unique tokens that appeared in memo but not in deck (warnings + infos)."""
        seen: list[str] = []
        for f in self.warnings + self.infos:
            if f.side == "only_in_memo" and f.token not in seen:
                seen.append(f.token)
        return seen

    @property
    def only_in_deck(self) -> list[str]:
        """Unique tokens that appeared in deck but not in memo (warnings + infos)."""
        seen: list[str] = []
        for f in self.warnings + self.infos:
            if f.side == "only_in_deck" and f.token not in seen:
                seen.append(f.token)
        return seen

    @property
    def only_in_memo_economic(self) -> list[str]:
        """Unique ``only_in_memo`` tokens that the load-bearingness
        classifier promoted to the economic subset (issue #553).

        **Invariant**: ``set(only_in_memo_economic) ⊆ set(only_in_memo)``.
        A token in this list is **always** also recorded as an
        ``only_in_memo`` finding (a separate ``Finding`` with
        ``side="only_in_memo"``); the economic side is the *additional*
        sharper signal a reviser consults before bulk-dismissing the
        full ``only_in_memo`` set.

        v0 (Phase A) ships at ``severity="warning"`` (or ``"info"`` when
        the escape hatch suppresses the underlying ``only_in_memo``
        token). The economic-subset finding does NOT promote to
        ``"error"`` and does NOT contribute to the host review's
        ``lint_critical_flag``.

        Always empty on the deck-side direction (``only_in_deck``
        findings are never promoted) and always empty when the lint
        skipped.
        """
        seen: list[str] = []
        for f in self.warnings + self.infos:
            if f.side == "only_in_memo_economic" and f.token not in seen:
                seen.append(f.token)
        return seen

    @property
    def only_in_memo_quarantined(self) -> list[str]:
        """Unique ``only_in_memo`` tokens reframed as BRIEF-quarantined
        (issue #914) — deliberately, rule-mandated omissions rather than
        drift awaiting a port decision.

        **Invariant**: ``set(only_in_memo_quarantined) ⊆ set(only_in_memo)``.
        A token in this list is **always** also recorded as an
        ``only_in_memo`` finding; the quarantined side is the *additional*
        reframing signal. **Mutually exclusive with
        ``only_in_memo_economic``** — a quarantined token is NEVER also
        promoted to the economic subset, even when it would otherwise
        qualify (money/percent/unit_int near economic-context vocab); the
        quarantine reframing takes precedence over the economic promotion
        for the same token.

        Always empty when ``quarantine_corpus`` is empty (the default) —
        byte-identical to pre-#914 behavior — and always empty when the
        lint skipped.
        """
        seen: list[str] = []
        for f in self.warnings + self.infos:
            if f.side == "only_in_memo_quarantined" and f.token not in seen:
                seen.append(f.token)
        return seen

    @property
    def quarantine_violations(self) -> list[str]:
        """Unique tokens found in the **deck** body that a project BRIEF's
        ``quarantine:`` list forbids porting (issue #914) — a real
        hard-rule violation this lint did not previously detect.

        Independent of ``only_in_deck`` / ``only_in_memo``: fires whenever
        a quarantined token appears anywhere in the deck body, regardless
        of whether the same token also appears in the memo. Always empty
        when ``quarantine_corpus`` is empty (the default) and always
        empty when the lint skipped.
        """
        seen: list[str] = []
        for f in self.warnings + self.infos:
            if f.side == "quarantine_violation" and f.token not in seen:
                seen.append(f.token)
        return seen

    def to_summary(self) -> dict:
        """Shape that fits cleanly into the review ``_summary.md`` ``lint`` block.

        The shape includes BOTH ``memo_sibling`` and ``deck_sibling`` —
        the wrapper that produced the result sets one; the other stays
        ``None``. ``ran: false`` is the graceful-skip shape; ``ran: true``
        with zero findings means the lint ran and both bodies had a
        fully-shared hard-claim universe.
        """
        return {
            "ran": not self.skipped,
            "memo_sibling": self.memo_sibling,
            "deck_sibling": self.deck_sibling,
            "reason": self.reason,
            "warnings": len(self.warnings),
            "infos": len(self.infos),
            "only_in_memo": self.only_in_memo,
            "only_in_deck": self.only_in_deck,
            "only_in_memo_economic": self.only_in_memo_economic,
            "only_in_memo_quarantined": self.only_in_memo_quarantined,
            "quarantine_violations": self.quarantine_violations,
            "warnings_by_token": [f.to_dict() for f in self.warnings],
            "infos_by_token": [f.to_dict() for f in self.infos],
        }


# Extractors -------------------------------------------------------------------
#
# Each extractor is a compiled regex applied line-by-line to a markdown body.
# The captured *token* is the part that should be exactly-equal across both
# bodies — it deliberately strips surrounding qualifier prose so that, for
# example, "~50–60% completion" extracts as the percentage "50-60%" and
# matches against a deck body that says "see the 50-60% completion benchmark".
#
# v0 is intentionally conservative on extractor scope. False-positive volume
# is the most likely friction mode; we'd rather miss a real drift than fire
# a warning on every prose noun phrase. The unit vocabulary
# (:data:`UNIT_VOCABULARY`) is deliberately narrow for the same reason.


# Money: $193K, $126M, $193.5M, $8.99, $29.99. The leading $ is required.
# Optional thousands separators (``$1,250``) and decimal points. Trailing
# K/M/B (case-insensitive) is the magnitude marker. We **normalize** the
# captured token to uppercase magnitude marker so ``$50m`` and ``$50M``
# compare as equal.
_MONEY_RE = re.compile(
    r"\$\d+(?:,\d{3})*(?:\.\d+)?[KMBkmb]?",
)


# Percentages: 26.6%, 50%, 50-60%, 50–60% (en-dash). Captures the whole
# range. The range form is normalized so ``50–60%`` and ``50-60%`` compare
# as equal (en-dash → ASCII hyphen).
_PERCENT_RE = re.compile(
    r"\d+(?:\.\d+)?(?:\s*[–-]\s*\d+(?:\.\d+)?)?\s*%",
)


# Quarters / FY tags: Q1 FY24, FY2024, FY24. The ``20XX`` bare-year
# extractor is intentionally NOT included here — bare four-digit years
# fire too aggressively on prose (footnote dates, dollar amounts, etc.).
# Calendar years are picked up via the named-month-plus-year extractor
# below.
_QUARTER_FY_RE = re.compile(
    r"\b(?:Q[1-4]\s+)?FY\d{2,4}\b",
)


# Named months + year: Jan 2025, April 2024, September 2023. Both
# 3-letter and full-word month names are accepted. Two-word "Sept 2023"
# vs "September 2023" do NOT normalize together in v0 — the deferred
# semantic-equivalence layer would catch that case.
_MONTH_NAMES = (
    "January", "February", "March", "April", "May", "June",
    "July", "August", "September", "October", "November", "December",
    "Jan", "Feb", "Mar", "Apr", "Jun", "Jul", "Aug", "Sep", "Sept", "Oct", "Nov", "Dec",
)
_MONTH_YEAR_RE = re.compile(
    r"\b(?:" + "|".join(_MONTH_NAMES) + r")\s+20\d{2}\b",
)


# ALL-CAPS acronyms (length 2-6): FTC, SFMTA, NYC, LOI, ARR, TAM, FY (FY
# also matched by the quarter regex; that's fine, we de-dupe at the set
# level). Length bound 2-6 rejects prose ALL-CAPS like single-letter "I"
# and over-long shouting. Word boundaries enforce token-ness.
_ACRONYM_RE = re.compile(
    r"\b[A-Z]{2,6}\b",
)


# Unit-bearing integers: 8 pilots, 50 LOIs, 250k plants. The unit
# vocabulary is **deliberately narrow** in v0 — adding to it should be
# canary-driven, not speculative. The leading number captures optional
# thousands separators and an optional "k"/"K"/"M"/"B" magnitude marker.
UNIT_VOCABULARY: tuple[str, ...] = (
    "users", "customers", "LOIs", "LOI", "pilots", "pilot",
    "design partners", "design partner",
    "completion", "completions",
    "reduction", "reductions",
    "plants", "factories",
    "engineers", "engineer",
    "founders", "founder",
    "deals", "deal",
)
# Build the alternation with longer phrases first so ``design partners``
# wins over ``partners`` alone.
_UNIT_ALT = "|".join(sorted(UNIT_VOCABULARY, key=lambda s: -len(s)))
_UNIT_INT_RE = re.compile(
    r"\b\d+(?:,\d{3})*(?:\.\d+)?[KkMmBb]?\s+(?:" + _UNIT_ALT + r")\b",
)


#: Economic-context vocabulary — the load-bearingness filter (issue #553).
#:
#: A token from a ``money`` / ``percent`` / ``unit_int`` extractor that
#: co-occurs (same line, ±3 lines) with one of these terms in the memo
#: source is promoted to the new ``only_in_memo_economic`` finding side.
#: Conservative seed list per the canary brief: enough to catch the Docent
#: failure shape (a contribution-margin / attach-rate number near
#: unit-economics prose) without firing on every memo noun phrase.
#: Calibration knob — narrow / widen via canary feedback. Bare acronym
#: tokens (e.g., ``FTC``) are NEVER promoted; only money/percent/unit_int
#: rule-label tokens qualify, and only when the co-occurrence check fires.
ECONOMIC_CONTEXT_VOCABULARY: tuple[str, ...] = (
    "attach", "attach rate",
    "ARPU", "ACV", "ARR", "MRR", "LTV", "CAC",
    "margin", "contribution margin", "gross margin", "net margin",
    "payback", "payback period",
    "kill threshold", "kill-threshold",
    "unit economics", "unit-economics",
    "take rate", "take-rate", "rev-share", "rev share", "revenue share",
    "pricing", "price",
    "conversion", "conversion rate",
    "churn", "retention",
    "GMV", "TAM", "SAM", "SOM",
)

#: Proximity window for the load-bearingness co-occurrence check, in lines
#: above and below the token's line. v0 ships at ±3 lines per the curator
#: brief. A memo that buries an attach-rate number more than 3 lines from
#: the word "attach" misses promotion (false-negative-tolerant by design).
#: Canary-driven follow-on may widen.
ECONOMIC_CONTEXT_PROXIMITY_LINES: int = 3

#: Rule labels whose tokens are eligible for promotion. Acronym /
#: quarter_fy / month_year tokens are NEVER promoted: the conservative cut
#: targets quantitative substance (money / percent / unit-bearing integers)
#: only. See issue #553's "Bare acronyms NOT promoted" contract.
_ECONOMIC_ELIGIBLE_RULE_LABELS: frozenset[str] = frozenset(
    {"money", "percent", "unit_int"}
)


#: Ordered tuple of (rule-label, compiled-regex). Order is informational; the
#: actual lint logic unions all matches into a token set per body.
EXTRACTORS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("money", _MONEY_RE),
    ("percent", _PERCENT_RE),
    ("quarter_fy", _QUARTER_FY_RE),
    ("month_year", _MONTH_YEAR_RE),
    ("acronym", _ACRONYM_RE),
    ("unit_int", _UNIT_INT_RE),
)


# Token normalization ----------------------------------------------------------


def _normalize_token(token: str) -> str:
    """Normalize a captured token so equivalent surface forms compare equal.

    v0 normalization is **deliberately minimal**: just enough to fold the
    common ASCII / Unicode dash variants and to canonicalize whitespace
    inside captured ranges. Semantic equivalence (``$193K`` ↔ ``$193,000``)
    is the deferred normalization layer.

    Concrete rules:

    - Replace en-dash (``\\u2013``) and em-dash (``\\u2014``) with ASCII
      hyphen so ``50–60%`` and ``50-60%`` are the same token.
    - Collapse internal whitespace to a single space so ``Q1  FY24`` and
      ``Q1 FY24`` are the same token.
    - Uppercase trailing magnitude markers on money (``$50m`` → ``$50M``).
    - Strip a trailing period (sentence-end punctuation often sticks to
      the last captured token, e.g., ``FTC.``).
    """
    t = token.strip()
    t = t.replace("–", "-").replace("—", "-")
    t = re.sub(r"\s+", " ", t)
    # Uppercase a trailing money magnitude marker.
    m = re.match(r"^(\$\d+(?:,\d{3})*(?:\.\d+)?)([kmb])$", t)
    if m:
        t = m.group(1) + m.group(2).upper()
    # Strip a trailing period (commonly attached when the token ends a
    # sentence: "the FTC." → "FTC").
    if t.endswith("."):
        t = t[:-1]
    return t


# Token extraction -------------------------------------------------------------


@dataclass
class _Hit:
    """An extracted token + the 1-based line it appeared on."""

    line: int
    token: str
    rule_label: str  # the extractor that produced the match — informational


def _extract_tokens(source: str) -> list[_Hit]:
    """Apply every extractor to ``source`` and return a flat list of hits.

    Each match is captured as a ``_Hit(line=1-based-line, token=normalized,
    rule_label=...)``. Duplicates within the same body are preserved here —
    the caller de-dupes at the set-comparison step. Lint-disable directives
    themselves are scrubbed from the line before extraction (otherwise the
    rule-name inside the comment would appear as an ALL-CAPS acronym match
    in the parity set).
    """
    hits: list[_Hit] = []
    for line_idx, line in enumerate(source.splitlines(), start=1):
        # Scrub any anvil-lint-disable directive from the line so its inner
        # rule name (e.g., ``deck_memo_parity``) does not surface as a hit.
        scrubbed = _LINT_DISABLE_RE.sub("", line)
        for label, pattern in EXTRACTORS:
            for m in pattern.finditer(scrubbed):
                raw = m.group(0)
                token = _normalize_token(raw)
                if not token:
                    continue
                hits.append(_Hit(line=line_idx, token=token, rule_label=label))
    return hits


# Lint-disable handling --------------------------------------------------------


def _collect_disabled_tokens(source: str, rule: str) -> set[str]:
    """Return the set of normalized tokens whose parity check is suppressed.

    Two placements honored (mirrors ``memo_image_refs._collect_disabled_lines``
    adapted to the parity model):

    1. **Same line**: ``<!-- anvil-lint-disable: <rule> -->`` on the
       same line as the token suppresses **every token on that line** for the
       parity rule.
    2. **Line above**: a standalone directive on the immediately preceding
       line (only whitespace allowed alongside) suppresses every token on
       the next non-blank, non-directive line.

    Returns the set of **normalized token strings** so the caller can
    downgrade matching findings to ``info`` without re-running the
    extractor for the suppressed lines.
    """
    disabled_lines: set[int] = set()
    lines = source.splitlines()
    for i, line in enumerate(lines):
        for m in _LINT_DISABLE_RE.finditer(line):
            rules = {r.strip() for r in m.group("rules").split(",") if r.strip()}
            if rule not in rules:
                continue
            # Same-line: suppress every token on this line.
            disabled_lines.add(i + 1)
            # If the directive is the ONLY content on the line (no leading
            # or trailing non-whitespace), also suppress the next non-blank
            # non-directive line — same shape as memo_image_refs.
            head = line[: m.start()].strip()
            tail = line[m.end():].strip()
            if head or tail:
                continue
            for j in range(i + 1, len(lines)):
                next_line = lines[j]
                if not next_line.strip():
                    continue
                if _LINT_DISABLE_RE.search(next_line):
                    continue
                disabled_lines.add(j + 1)
                break

    # Resolve disabled lines → disabled normalized tokens.
    disabled_tokens: set[str] = set()
    for line_idx, line in enumerate(lines, start=1):
        if line_idx not in disabled_lines:
            continue
        scrubbed = _LINT_DISABLE_RE.sub("", line)
        for _label, pattern in EXTRACTORS:
            for m in pattern.finditer(scrubbed):
                disabled_tokens.add(_normalize_token(m.group(0)))
    return disabled_tokens


# Diagnostic message construction ----------------------------------------------


def _build_message_deck_side(token: str, side: str, line_no: int) -> str:
    """Deck-side diagnostic. Preserved verbatim from the pre-promotion
    ``anvil/skills/deck/lib/parity_lint._build_message``. The
    ``only_in_memo`` branch names the canary failure mode (the
    citation-clear insurer benchmark) so the Phase A → Phase B promotion
    conversation has a concrete anchor.

    The third side value ``"only_in_memo_economic"`` (issue #553) emits a
    sharper "deck dropped substance the memo carried" framing the
    reviser consults before bulk-dismissing the broader ``only_in_memo``
    set. The classifier promotes a strict subset of ``only_in_memo``
    tokens to this side; the underlying ``only_in_memo`` finding for the
    same token is still emitted (the economic side is additional
    surfacing, not a replacement).

    The fourth and fifth side values, ``"only_in_memo_quarantined"`` and
    ``"quarantine_violation"`` (issue #914), are the BRIEF-quarantine
    surface — see the module docstring's "Quarantine corpus" section.
    """
    if side == "only_in_memo_economic":
        return (
            f"**Economic substance dropped from deck.** Hard claim `{token}` "
            f"appears in memo (line {line_no}) near unit-economics / pricing "
            f"context (see `ECONOMIC_CONTEXT_VOCABULARY`) but is absent from "
            f"the sibling deck. This is a sharper warning than the broader "
            f"`only_in_memo` class: a load-bearing economic number the deck "
            f"dropped. Was the drop deliberate? If yes, document with "
            f"`<!-- anvil-lint-disable: deck_memo_parity -->`; if no, port "
            f"the claim into the deck on next `deck-revise`. Do NOT bulk-"
            f"dismiss as ordinary drift (warning only in v0, but the "
            f"reviser should consult this subset before accepting the "
            f"broader memo↔deck divergence)."
        )
    if side == "only_in_memo_quarantined":
        return (
            f"**Correctly absent per BRIEF hard rule — do not port.** Hard "
            f"claim `{token}` appears in memo (line {line_no}) but is listed "
            f"on the project BRIEF's `quarantine:` surface. This is NOT a "
            f"'should you port this?' divergence — the omission from the "
            f"deck is deliberate and rule-mandated. Do not port `{token}` "
            f"into the deck on `deck-revise`. Note: quarantine matches "
            f"literal tokens only — a derived form of this figure (e.g. an "
            f"arithmetic product of a quarantined rate) is NOT caught by "
            f"this lint; check derivations manually."
        )
    if side == "quarantine_violation":
        return (
            f"**BRIEF hard-rule violation: quarantined figure in deck.** "
            f"Hard claim `{token}` appears in the deck (line {line_no}) but "
            f"is listed on the project BRIEF's `quarantine:` surface — a "
            f"hard rule forbids porting this figure. This is an actionable "
            f"violation, not ordinary drift: remove or replace `{token}` on "
            f"the next `deck-revise` with the BRIEF-mandated figure."
        )
    if side == "only_in_memo":
        return (
            f"Hard claim `{token}` appears in memo (line {line_no}) but not "
            f"in the sibling deck. Either reconcile (add to deck on next "
            f"`deck-revise`), document the deliberate omission with "
            f"`<!-- anvil-lint-disable: deck_memo_parity -->`, or accept "
            f"the divergence (warning only in v0). Canary: Citation Clear "
            f"memo.4 introduced a `~50–60% completion` insurer benchmark "
            f"absent from deck.3 — exactly this shape."
        )
    return (
        f"Hard claim `{token}` appears in deck (line {line_no}) but not "
        f"in the sibling memo. Either reconcile (add to memo on next "
        f"`memo-revise`), document the deliberate divergence with "
        f"`<!-- anvil-lint-disable: deck_memo_parity -->`, or accept "
        f"the divergence (warning only in v0)."
    )


def _build_message_memo_side(token: str, side: str, line_no: int) -> str:
    """Memo-side diagnostic. Preserved verbatim from the pre-promotion
    ``anvil/skills/memo/lib/parity_lint._build_message``. The message
    frames the parity drift from the **memo-side perspective**:
    ``only_in_deck`` is the load-bearing failure mode (deck pulled
    ahead, memo did not notice); ``only_in_memo`` is the local-only
    claim (memo says X, deck does not — informational from the memo
    POV, since the deck-side lint would catch this in the symmetric
    direction).

    The third side value ``"only_in_memo_economic"`` (issue #553) emits
    on the memo side too — informational from the memo POV (the memo is
    rich, the deck is thin; from this POV no memo-revise action is
    required), but the schema-parity contract requires the side and the
    classifier output to surface symmetrically across both wrappers.

    The fourth and fifth side values, ``"only_in_memo_quarantined"`` and
    ``"quarantine_violation"`` (issue #914), likewise surface on the memo
    side for schema parity — see the module docstring's "Quarantine
    corpus" section.
    """
    if side == "only_in_memo_economic":
        return (
            f"**Economic substance the deck dropped.** Hard claim `{token}` "
            f"appears in memo (line {line_no}) near unit-economics / pricing "
            f"context (see `ECONOMIC_CONTEXT_VOCABULARY`) but is absent from "
            f"the sibling deck. From the memo-side POV this is informational "
            f"— the memo is the rich body; this signal is actionable for "
            f"the deck-revise reviser, not the memo-revise reviser. "
            f"Surfacing on both sides preserves schema parity (warning only "
            f"in v0)."
        )
    if side == "only_in_memo_quarantined":
        return (
            f"**Correctly absent per BRIEF hard rule — do not port.** Hard "
            f"claim `{token}` appears in memo (line {line_no}) but is listed "
            f"on the project BRIEF's `quarantine:` surface. From the "
            f"memo-side POV this is informational — the memo is allowed to "
            f"carry the quarantined figure; the rule forbids it on the "
            f"deck. This is NOT a 'should you port this?' divergence. Note: "
            f"quarantine matches literal tokens only — a derived form of "
            f"this figure is NOT caught by this lint."
        )
    if side == "quarantine_violation":
        return (
            f"**BRIEF hard-rule violation: quarantined figure in deck.** "
            f"Hard claim `{token}` appears in the sibling deck but is listed "
            f"on the project BRIEF's `quarantine:` surface — a hard rule "
            f"forbids porting this figure. From the memo-side POV this is "
            f"actionable for the `deck-revise` reviser, not `memo-revise`; "
            f"surfacing on both sides preserves schema parity."
        )
    if side == "only_in_deck":
        return (
            f"Hard claim `{token}` appears in deck (line {line_no}) but not "
            f"in the sibling memo. Either reconcile (add to memo on next "
            f"`memo-revise`), document the deliberate divergence with "
            f"`<!-- anvil-lint-disable: memo_deck_parity -->`, or accept "
            f"the divergence (warning only in v0). Canary: Citation Clear "
            f"memo.4 ↔ deck.3 — the symmetric direction of the "
            f"`~50–60% completion` insurer-benchmark drift surfaced in "
            f"issue #200 — exactly this shape."
        )
    return (
        f"Hard claim `{token}` appears in memo (line {line_no}) but not "
        f"in the sibling deck. Either reconcile (add to deck on next "
        f"`deck-revise`), document the deliberate omission with "
        f"`<!-- anvil-lint-disable: memo_deck_parity -->`, or accept "
        f"the divergence (warning only in v0)."
    )


def _build_message(token: str, side: str, line_no: int, rule: str) -> str:
    """Dispatch to the deck-side or memo-side message builder based on
    ``rule``. Centralizes the two skill-local variants while preserving
    their byte-identical canary-anchor wording (both grep-pinned by
    ``test_citation_clear_*`` tests on each side)."""
    if rule == "memo_deck_parity":
        return _build_message_memo_side(token, side, line_no)
    return _build_message_deck_side(token, side, line_no)


# Figure corpus (issue #623) ---------------------------------------------------

#: Raw numeric-substring extractor shared by the figure corpus builder and the
#: per-token numeric stripper. Matches integer / decimal / thousands-separated
#: runs (``2``, ``2.50``, ``26.6``, ``2,500``) but never a bare sign or unit.
#: Deliberately format-agnostic: applied to raw CSV text it finds cell values
#: regardless of surrounding ``$`` / ``%`` / label decoration.
_FIGURE_NUMERIC_RE = re.compile(r"\d+(?:[.,]\d+)*")


def _extract_figure_corpus(deck_version_dir: Path) -> frozenset[str]:
    """Read raw numeric values out of ``figures/src/*.csv`` under a deck dir.

    Issue #623: dense economic tables are the *designed* home for numbers on a
    figure-heavy deck — the ``deck-design`` rubric rewards moving a P&L table
    into a chart, and those charts are rendered by ``deck-figures`` from
    ``figures/src/*.csv``. The text-only parity lint cannot see numbers that
    live inside a rendered PNG, so it false-promotes them to
    ``only_in_memo_economic`` ("economic substance dropped"). This helper gives
    the classifier a second match surface: the CSV sources that the figures
    (and the auditor's re-run) already trace to 1:1.

    Walks ``deck_version_dir / "figures" / "src"`` for ``*.csv`` files, reads
    each as text, and unions every numeric substring (``re.findall`` over
    :data:`_FIGURE_NUMERIC_RE`) into a frozenset of raw numeric strings
    (``{"2.50", "3.25", "26.6"}``). Stdlib only — no CSV parsing, just raw
    substring extraction so a formatted cell (``$2.50``) still yields ``2.50``.

    Graceful by contract: returns :func:`frozenset` (empty) when the directory
    is missing, no CSVs exist, or any file is unreadable. An empty corpus makes
    the downstream classifier byte-identical to its pre-#623 behavior.
    """
    if not isinstance(deck_version_dir, Path):
        deck_version_dir = Path(deck_version_dir)
    src_dir = deck_version_dir / "figures" / "src"
    if not src_dir.is_dir():
        return frozenset()
    corpus: set[str] = set()
    try:
        csv_paths = sorted(src_dir.glob("*.csv"))
    except OSError:
        return frozenset()
    for csv_path in csv_paths:
        try:
            text = csv_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            # A single unreadable CSV must not sink the whole corpus — the
            # graceful-degradation contract is per-file, not per-directory.
            continue
        for m in _FIGURE_NUMERIC_RE.finditer(text):
            corpus.add(m.group(0))
    return frozenset(corpus)


def _strip_token_numeric(token: str) -> list[str]:
    """Expose the raw numeric component(s) of a parity token.

    Strips currency / percent / unit decoration to surface the bare numbers so
    a token can be tested against the figure corpus built by
    :func:`_extract_figure_corpus`:

    - ``"$2.50"`` → ``["2.50"]``
    - ``"26.6%"`` → ``["26.6"]``
    - ``"50-60%"`` → ``["50", "60"]`` (range → both endpoints)
    - ``"8 pilots"`` → ``["8"]``
    - ``"FTC"`` → ``[]`` (acronym — no numeric component)

    Returns an empty list for numeric-free tokens (acronyms, quarters); those
    are never promotion-eligible anyway, so the empty list is a safe no-op.
    """
    return _FIGURE_NUMERIC_RE.findall(token)


# Quarantine corpus (issue #914) ------------------------------------------------


def _extract_quarantine_corpus(project_dir: Path) -> frozenset[str]:
    """Read the project ``BRIEF.md``'s ``quarantine:`` surface and return
    it as a normalized token frozenset.

    ``project_dir`` is the project root — the parent of the thread root,
    i.e. the directory containing ``BRIEF.md`` (same discovery convention
    as ``load_rubric_overrides_for_slug``; see the two ``*-review.md``
    command files' project-root discovery prose). Each configured
    quarantine entry is passed through :func:`_normalize_token` so it
    matches the same normalized surface the extractors produce (dash
    unification, uppercased money magnitude marker, trailing-period
    strip) — a BRIEF author writing ``quarantine: ["$400m"]`` still
    matches a memo token normalized to ``"$400M"``.

    Graceful by contract, mirroring :func:`_extract_figure_corpus`:
    returns an empty frozenset when ``project_dir`` has no ``BRIEF.md``,
    the BRIEF fails to parse (malformed frontmatter/schema — a broken
    project BRIEF must not sink the parity lint), or the BRIEF has no
    ``quarantine:`` key. An empty corpus makes the downstream classifier
    byte-identical to its pre-#914 behavior.
    """
    if not isinstance(project_dir, Path):
        project_dir = Path(project_dir)
    try:
        from anvil.lib.project_brief import load_project_brief
    except ImportError:
        return frozenset()
    try:
        brief = load_project_brief(project_dir)
    except ValueError:
        return frozenset()
    if brief is None or not brief.quarantine:
        return frozenset()
    return frozenset(
        _normalize_token(t) for t in brief.quarantine if t and t.strip()
    )


# Load-bearingness classifier (issue #553) -------------------------------------


def _classify_economic_tokens(
    only_in_memo_tokens: set[str],
    memo_hits: list[_Hit],
    memo_source: str,
    figure_corpus: frozenset[str] = frozenset(),
) -> set[str]:
    """Promote a strict subset of ``only_in_memo`` tokens to the
    load-bearing-economic class (issue #553).

    Conservative cut: a token qualifies iff (a) its extractor rule label
    is one of :data:`_ECONOMIC_ELIGIBLE_RULE_LABELS` (``money`` /
    ``percent`` / ``unit_int``) AND (b) the memo source contains an
    :data:`ECONOMIC_CONTEXT_VOCABULARY` term within
    :data:`ECONOMIC_CONTEXT_PROXIMITY_LINES` lines of the token's first
    appearance in the memo. Acronym / quarter_fy / month_year tokens are
    NEVER promoted (per the issue #553 "bare acronyms NOT promoted"
    contract).

    Returns the set of normalized token strings to promote. Always a
    subset of ``only_in_memo_tokens`` (invariant enforced by the caller;
    a token that does not appear in ``only_in_memo_tokens`` is never
    returned).

    The check is case-insensitive on the vocabulary side (the memo's
    "ARPU" matches the vocab's "ARPU" exactly, while "Attach Rate" in
    the memo matches the vocab's "attach rate" via lower-casing). Lint-
    disable directives on the memo line are scrubbed before the
    co-occurrence check so the directive's inner rule name does not
    surface as fake vocab.

    Figure-carried suppression (issue #623): ``figure_corpus`` is the set
    of raw numeric strings pulled from the deck's ``figures/src/*.csv``
    sources (see :func:`_extract_figure_corpus`). When a token would
    otherwise be promoted but any of its numeric components
    (:func:`_strip_token_numeric`) appears in ``figure_corpus``, promotion
    is **skipped** — the number is present in the deck via a rendered
    chart, so its economic substance was not dropped. The token still
    surfaces as an undifferentiated ``only_in_memo`` finding (the caller
    layers the economic finding additively, so a skipped promotion simply
    omits the sharper class). An empty ``figure_corpus`` (the default, and
    the memo-side wrapper's only path) makes this a no-op — behavior is
    byte-identical to the pre-#623 classifier.
    """
    if not only_in_memo_tokens:
        return set()

    # Build vocab matchers: compile a per-term whole-word regex so
    # short acronyms (``ARR``, ``CAC``, ``GMV``) do not false-positive
    # on substring matches inside ordinary prose (``carrier`` contains
    # ``arr``; ``vacate`` contains ``cac``). Multi-word terms get
    # whitespace-tolerant matching (``contribution margin`` matches
    # both ``contribution margin`` and ``contribution  margin``). Case-
    # insensitive: ``Attach`` in prose matches the vocab's ``attach``.
    vocab_patterns: list[re.Pattern[str]] = []
    for term in ECONOMIC_CONTEXT_VOCABULARY:
        # Escape regex metachars then split on internal whitespace so
        # multi-word terms tolerate any whitespace run between tokens.
        escaped_parts = [re.escape(p) for p in term.split()]
        body = r"\s+".join(escaped_parts) if len(escaped_parts) > 1 else escaped_parts[0]
        vocab_patterns.append(
            re.compile(r"(?<![A-Za-z0-9])" + body + r"(?![A-Za-z0-9])", re.IGNORECASE)
        )

    # Pre-scrub source lines (drop lint-disable directives so their
    # internal rule name does not match against the vocab).
    scrubbed_lines = [
        _LINT_DISABLE_RE.sub("", line)
        for line in memo_source.splitlines()
    ]

    def _line_has_context(line_idx_1based: int) -> bool:
        lo = max(1, line_idx_1based - ECONOMIC_CONTEXT_PROXIMITY_LINES)
        hi = min(len(scrubbed_lines), line_idx_1based + ECONOMIC_CONTEXT_PROXIMITY_LINES)
        for i in range(lo, hi + 1):
            haystack = scrubbed_lines[i - 1]
            for pattern in vocab_patterns:
                if pattern.search(haystack):
                    return True
        return False

    promoted: set[str] = set()
    # Iterate ALL hits (not just the first) for each candidate token —
    # a token can appear multiple times in the memo; promotion fires if
    # ANY appearance is in economic context.
    for h in memo_hits:
        if h.token in promoted:
            continue
        if h.token not in only_in_memo_tokens:
            continue
        if h.rule_label not in _ECONOMIC_ELIGIBLE_RULE_LABELS:
            continue
        if not _line_has_context(h.line):
            continue
        # Figure-carried suppression (issue #623): if the token's numeric
        # value lives in the deck's figures/src CSVs, the number is present
        # on the slide via a chart — do NOT escalate to the economic class.
        if figure_corpus and any(
            n in figure_corpus for n in _strip_token_numeric(h.token)
        ):
            continue
        promoted.add(h.token)
    return promoted


# Public API -------------------------------------------------------------------


def lint_source(
    deck_source: str,
    memo_source: str,
    *,
    rule: str = "deck_memo_parity",
    figure_corpus: frozenset[str] = frozenset(),
    quarantine_corpus: frozenset[str] = frozenset(),
) -> LintResult:
    """Run the parity lint over two in-memory body strings.

    Default ``rule`` preserves deck-side semantics so the existing
    deck-side ``lint_source(deck_source, memo_source)`` call is
    byte-compatible. Memo-side wrapper passes ``rule="memo_deck_parity"``
    via its thin re-export.

    ``figure_corpus`` (issue #623) is an optional set of raw numeric
    strings pulled from the deck's ``figures/src/*.csv`` sources. It is
    threaded into the economic classifier to suppress false
    ``only_in_memo_economic`` promotions for numbers that are present on
    the deck via a rendered chart. Defaulting to an empty frozenset keeps
    this call byte-identical to its pre-#623 form for every existing
    consumer (the citation-clear canary anchor calls this API directly with
    no figure corpus).

    ``quarantine_corpus`` (issue #914) is an optional set of normalized
    tokens a project BRIEF's ``quarantine:`` list forbids porting from
    memo to deck (see :func:`_extract_quarantine_corpus`). It has two
    effects, both additive to the v0 shape: (1) a quarantined
    ``only_in_memo`` token is excluded from ``only_in_memo_economic``
    promotion and instead surfaces under ``side="only_in_memo_quarantined"``
    — "correctly absent per BRIEF hard rule," not a divergence awaiting a
    port decision; (2) a quarantined token found anywhere in the deck body
    raises a NEW ``side="quarantine_violation"`` finding — a real hard-rule
    violation. Defaulting to an empty frozenset keeps this call
    byte-identical to its pre-#914 form for every existing consumer.

    This is the unit-testable core; the wrappers
    (``lint_deck_memo_parity`` / ``lint_memo_deck_parity``) handle the
    graceful-skip path. Both source strings are required — the caller is
    responsible for the sibling-discovery step and for invoking the skip
    path when no sibling exists.

    Returns a :class:`LintResult` with one warning per token in
    ``only_in_memo`` ∪ ``only_in_deck``, downgraded to ``info`` if the
    line carrying the token had ``<!-- anvil-lint-disable: <rule> -->``
    set (or on the line directly above).
    """
    result = LintResult()

    deck_hits = _extract_tokens(deck_source)
    memo_hits = _extract_tokens(memo_source)

    deck_tokens = {h.token for h in deck_hits}
    memo_tokens = {h.token for h in memo_hits}

    deck_disabled = _collect_disabled_tokens(deck_source, rule)
    memo_disabled = _collect_disabled_tokens(memo_source, rule)

    # only_in_memo: tokens present in memo but absent from deck.
    only_in_memo_tokens = memo_tokens - deck_tokens
    # Track the first line each token appears on for the diagnostic.
    memo_first_line: dict[str, int] = {}
    for h in memo_hits:
        if h.token in only_in_memo_tokens and h.token not in memo_first_line:
            memo_first_line[h.token] = h.line

    # Load-bearingness classifier (issue #553): promote the subset of
    # only_in_memo_tokens whose memo-side appearance co-occurs with
    # ECONOMIC_CONTEXT_VOCABULARY within ±N lines AND whose extractor
    # rule label is money / percent / unit_int. The promoted subset
    # is layered ADDITIVELY on top of only_in_memo — every promoted
    # token gets BOTH a side="only_in_memo" finding AND a
    # side="only_in_memo_economic" finding. The escape hatch applies
    # symmetrically (a suppressed only_in_memo token's promoted finding
    # is also info, not warning).
    economic_promoted = _classify_economic_tokens(
        only_in_memo_tokens, memo_hits, memo_source, figure_corpus
    )
    # Quarantine reframing (issue #914): a quarantined token is NEVER
    # promoted to only_in_memo_economic, even when it would otherwise
    # qualify — the quarantine reframe below takes precedence over the
    # economic-substance framing for the same token.
    if quarantine_corpus:
        economic_promoted -= quarantine_corpus

    for token in sorted(only_in_memo_tokens):
        line_no = memo_first_line.get(token, 0)
        suppressed = token in memo_disabled
        finding = Finding(
            line=line_no,
            rule=rule,
            severity="info" if suppressed else "warning",
            message=_build_message(token, "only_in_memo", line_no, rule),
            token=token,
            side="only_in_memo",
        )
        if suppressed:
            result.infos.append(finding)
        else:
            result.warnings.append(finding)

        # Layer the load-bearing-economic finding on top, when promoted.
        # Severity tracks the underlying only_in_memo finding's
        # severity — a suppressed token's economic surfacing is also
        # info, so the escape hatch needs no second mechanism.
        if token in economic_promoted:
            econ_finding = Finding(
                line=line_no,
                rule=rule,
                severity="info" if suppressed else "warning",
                message=_build_message(token, "only_in_memo_economic", line_no, rule),
                token=token,
                side="only_in_memo_economic",
            )
            if suppressed:
                result.infos.append(econ_finding)
            else:
                result.warnings.append(econ_finding)

        # Quarantine reframing (issue #914): layer the reframed
        # "correctly absent per BRIEF hard rule" finding on top instead
        # of (never alongside) the economic promotion. Severity mirrors
        # the underlying only_in_memo finding's severity — the two
        # mechanisms compose, matching the economic-promotion contract.
        if token in quarantine_corpus:
            quarantine_finding = Finding(
                line=line_no,
                rule=rule,
                severity="info" if suppressed else "warning",
                message=_build_message(
                    token, "only_in_memo_quarantined", line_no, rule
                ),
                token=token,
                side="only_in_memo_quarantined",
            )
            if suppressed:
                result.infos.append(quarantine_finding)
            else:
                result.warnings.append(quarantine_finding)

    # only_in_deck: symmetric — tokens present in deck but absent from memo.
    only_in_deck_tokens = deck_tokens - memo_tokens
    deck_first_line: dict[str, int] = {}
    for h in deck_hits:
        if h.token in only_in_deck_tokens and h.token not in deck_first_line:
            deck_first_line[h.token] = h.line

    for token in sorted(only_in_deck_tokens):
        line_no = deck_first_line.get(token, 0)
        suppressed = token in deck_disabled
        finding = Finding(
            line=line_no,
            rule=rule,
            severity="info" if suppressed else "warning",
            message=_build_message(token, "only_in_deck", line_no, rule),
            token=token,
            side="only_in_deck",
        )
        if suppressed:
            result.infos.append(finding)
        else:
            result.warnings.append(finding)

    # Quarantine violation (issue #914): a quarantined token appearing
    # ANYWHERE in the deck body — not just the only_in_deck subset — is a
    # real hard-rule violation the lint did not previously detect. Fires
    # independently of whether the same token also appears in the memo
    # (a token can be both `only_in_deck` AND `quarantine_violation`, or
    # shared with the memo AND `quarantine_violation`).
    if quarantine_corpus:
        deck_quarantine_first_line: dict[str, int] = {}
        for h in deck_hits:
            if h.token in quarantine_corpus and h.token not in deck_quarantine_first_line:
                deck_quarantine_first_line[h.token] = h.line
        for token in sorted(deck_quarantine_first_line):
            line_no = deck_quarantine_first_line[token]
            suppressed = token in deck_disabled
            violation_finding = Finding(
                line=line_no,
                rule=rule,
                severity="info" if suppressed else "warning",
                message=_build_message(token, "quarantine_violation", line_no, rule),
                token=token,
                side="quarantine_violation",
            )
            if suppressed:
                result.infos.append(violation_finding)
            else:
                result.warnings.append(violation_finding)

    return result


def lint_deck_memo_parity(
    deck_version_dir: Path,
    memo_version_dir: Path | None,
) -> LintResult:
    """Run the parity lint against a ``<thread>.{N}/`` deck version dir.

    ``memo_version_dir`` is the sibling memo version directory to compare
    against, or ``None`` when no memo sibling exists (the single-pipeline
    case). The lint **graceful-skips** when ``memo_version_dir`` is
    ``None``, when the deck source is missing, or when the memo source
    inside ``memo_version_dir`` is missing — the absence of either body
    is not a lint error, it's a structural skip recorded in the result.

    Discovery contract (responsibility-split with the caller):
        Sibling-memo-version discovery is the **caller's responsibility**
        in v0 (``deck-review`` step 5d performs the lookup using the
        convention documented in the issue body: highest-version
        ``<thread>.{M}/memo.md`` next to the deck version dir). Centralizing
        that lookup in ``anvil/lib/parity.py`` remains queued.
    """
    if not isinstance(deck_version_dir, Path):
        deck_version_dir = Path(deck_version_dir)
    if memo_version_dir is not None and not isinstance(memo_version_dir, Path):
        memo_version_dir = Path(memo_version_dir)

    if memo_version_dir is None:
        return LintResult(
            skipped=True,
            reason="no memo sibling found at portfolio root; parity check inactive",
            memo_sibling=None,
        )

    deck_path = deck_version_dir / "deck.md"
    # Memo body filename echoes the memo thread slug per the issue #295
    # project-org model lock (``<memo-thread>/<memo-thread>.{N}/<memo-thread>.md``).
    # The memo thread slug is the memo version dir's parent directory name.
    memo_body_filename = f"{memo_version_dir.parent.name}.md"
    memo_path = memo_version_dir / memo_body_filename

    if not deck_path.is_file():
        return LintResult(
            skipped=True,
            reason=f"deck.md not found at {deck_path}",
            memo_sibling=str(memo_version_dir.resolve()),
        )
    if not memo_path.is_file():
        return LintResult(
            skipped=True,
            reason=f"{memo_body_filename} not found at {memo_path}",
            memo_sibling=str(memo_version_dir.resolve()),
        )

    deck_source = deck_path.read_text(encoding="utf-8")
    memo_source = memo_path.read_text(encoding="utf-8")

    # Issue #623: consult the deck's figures/src CSVs as a second match
    # surface so figure-carried numbers are not false-promoted to
    # only_in_memo_economic. Graceful-empty when no figures/src/ exists.
    figure_corpus = _extract_figure_corpus(deck_version_dir)

    # Issue #914: consult the project BRIEF.md's quarantine: surface —
    # project root is the parent of the deck thread root (same discovery
    # convention as load_rubric_overrides_for_slug). Graceful-empty when
    # no BRIEF.md exists or it carries no quarantine: key.
    quarantine_corpus = _extract_quarantine_corpus(deck_version_dir.parent.parent)

    result = lint_source(
        deck_source,
        memo_source,
        rule="deck_memo_parity",
        figure_corpus=figure_corpus,
        quarantine_corpus=quarantine_corpus,
    )
    result.memo_sibling = str(memo_version_dir.resolve())
    return result


def lint_memo_deck_parity(
    memo_version_dir: Path,
    deck_version_dir: Path | None,
) -> LintResult:
    """Run the parity lint against a ``<thread>.{N}/`` memo version dir.

    ``deck_version_dir`` is the sibling deck version directory to compare
    against, or ``None`` when no deck sibling exists (the single-pipeline
    case). The lint **graceful-skips** when ``deck_version_dir`` is
    ``None``, when the memo source is missing, or when the deck source
    inside ``deck_version_dir`` is missing — the absence of either body
    is not a lint error, it's a structural skip recorded in the result.

    Discovery contract (responsibility-split with the caller):
        Sibling-deck-version discovery is the **caller's responsibility**
        in v0 (``memo-review`` step 4d performs the lookup). Centralizing
        that lookup in ``anvil/lib/parity.py`` remains queued.
    """
    if not isinstance(memo_version_dir, Path):
        memo_version_dir = Path(memo_version_dir)
    if deck_version_dir is not None and not isinstance(deck_version_dir, Path):
        deck_version_dir = Path(deck_version_dir)

    if deck_version_dir is None:
        return LintResult(
            skipped=True,
            reason="no deck sibling found at portfolio root; parity check inactive",
            deck_sibling=None,
        )

    # Body filename echoes the thread slug per the issue #295 project-org
    # model lock (``<thread>/<thread>.{N}/<thread>.md``). The thread slug
    # is the version dir's parent directory name.
    memo_body_filename = f"{memo_version_dir.parent.name}.md"
    memo_path = memo_version_dir / memo_body_filename
    deck_path = deck_version_dir / "deck.md"

    if not memo_path.is_file():
        return LintResult(
            skipped=True,
            reason=f"{memo_body_filename} not found at {memo_path}",
            deck_sibling=str(deck_version_dir.resolve()),
        )
    if not deck_path.is_file():
        return LintResult(
            skipped=True,
            reason=f"deck.md not found at {deck_path}",
            deck_sibling=str(deck_version_dir.resolve()),
        )

    memo_source = memo_path.read_text(encoding="utf-8")
    deck_source = deck_path.read_text(encoding="utf-8")

    # Issue #914: consult the project BRIEF.md's quarantine: surface —
    # project root is the parent of the memo thread root, symmetric to
    # the deck-side wrapper's discovery. Graceful-empty when no BRIEF.md
    # exists or it carries no quarantine: key.
    quarantine_corpus = _extract_quarantine_corpus(memo_version_dir.parent.parent)

    # The memo-side wrapper passes the sources in deck/memo positional
    # order to the shared core, with ``rule="memo_deck_parity"`` to
    # select the memo-side rule label and diagnostic wording.
    result = lint_source(
        deck_source,
        memo_source,
        rule="memo_deck_parity",
        quarantine_corpus=quarantine_corpus,
    )
    result.deck_sibling = str(deck_version_dir.resolve())
    return result


def lint_parity(
    primary_path: Path,
    sibling_path: Path | None,
    primary_kind: Literal["deck", "memo"],
    sibling_kind: Literal["deck", "memo"],
) -> LintResult:
    """Unified parity wrapper. Dispatches to the deck-side or memo-side
    primary-artifact framing based on ``primary_kind``.

    v0 keeps the sibling-discovery contract on the caller (mirrors both
    existing wrappers); the unified signature is the seam future versions
    can grow into.

    Raises ``ValueError`` if the primary / sibling pair is not one of the
    supported (deck, memo) or (memo, deck) combinations.
    """
    if primary_kind == "deck" and sibling_kind == "memo":
        return lint_deck_memo_parity(primary_path, sibling_path)
    if primary_kind == "memo" and sibling_kind == "deck":
        return lint_memo_deck_parity(primary_path, sibling_path)
    raise ValueError(
        f"unsupported parity pair: primary={primary_kind!r}, sibling={sibling_kind!r}"
    )


__all__ = [
    "ECONOMIC_CONTEXT_PROXIMITY_LINES",
    "ECONOMIC_CONTEXT_VOCABULARY",
    "EXTRACTORS",
    "Finding",
    "LintResult",
    "RULES_DECK",
    "RULES_MEMO",
    "UNIT_VOCABULARY",
    "lint_source",
    "lint_deck_memo_parity",
    "lint_memo_deck_parity",
    "lint_parity",
]
