# Plain-language-first: explain before you name

This snippet codifies the **plain-language-first writing framework** (issue
#1042, Phase 1 of 3 — issue #1043) — the universal judgment-side rule that
**the purpose of writing is to help a reader learn or decide, not to
display expertise.** A technical term earns its place when it is more
precise than ordinary language, supports later reasoning, or lets the
reader connect the idea to an established literature. It should not
replace a clear explanation merely because it sounds professional. If
plain words carry the same meaning, prefer them.

This is **judgment-side guidance for drafters and reviewers**, not a
mechanical rule. `anvil/lib/rhetoric_lint.py` (the deterministic AI-tell /
trope / density scanner backing rubric dim 9 *Rhetorical economy*) has no
jargon-earns-its-place check, and by design cannot gain one — whether a
term is doing real semantic work is a reading-comprehension judgment a
regex scanner cannot make. See `tests/lib/test_rhetoric_lint.py`'s
`jargon_dense_unexplained` regression test for the fixture proving this
boundary: a polished, jargon-dense passage that scores **zero findings**
from the lint while still failing the plain-language test below.

**This is not a ban on jargon.** Some terms are exact and necessary. The
test is whether the term does real semantic work — see §"Terminology
exceptions" below.

## The 7-point framework

1. **State the idea in ordinary language before introducing formal
   notation or specialist labels.** A reader should be able to follow the
   first mention of a concept without already knowing its name. Lead with
   what the idea *does*, not with what it is *called*.

2. **Explain why the idea matters, preferably with a concrete example.**
   An abstract claim ("this improves reliability") lands weakly on its
   own; a concrete instance ("this catches the case where a rerun signs
   off on its own broken output") makes the stakes legible.

3. **Introduce a technical term only when it adds precision or useful
   connection.** A term earns its place when it (a) is more precise than
   the ordinary-language version, (b) supports reasoning later in the
   document (the reader will need to refer back to a compact handle), or
   (c) lets the reader connect the idea to an established literature or
   named prior work. Define it **at first load-bearing use** — the
   sentence where the term first matters to the argument, not a glossary
   appendix the reader has not reached yet.

4. **Keep the plain explanation even after naming the term.** The label
   is not the explanation. Once a term is introduced, later uses may rely
   on it, but the passage that introduces it must still carry the plain
   restatement alongside the name — a reader who skips the label should
   still be able to follow the sentence.

5. **Gather assumptions, caveats, and provenance in a suitable technical
   section when inserting them sentence-by-sentence would bury the main
   idea.** This is not license to omit qualification — it is a placement
   rule. A single provenance note at the body level plus a ledger
   (exhibit, appendix, footnote block) that enumerates the individual
   caveats keeps the main argument legible while keeping every caveat
   findable. (This mirrors the memo rubric's existing "redundant hedging"
   convention — see `anvil/skills/memo/rubric.md` §"Redundant hedging" —
   which prices repeated inline restatement of an already-ledgered caveat
   under dim 9 rather than crediting it under the sourcing dimension.)

6. **Allow more words when those words teach.** Rhetorical economy
   penalizes padding and repetition, not patient explanation. A longer
   passage that walks a reader from an ordinary-language statement to a
   precise technical one is not bloat — it is the artifact doing its job.
   See §"Interaction with dim 9" below for how this composes with the
   existing rubric guidance.

7. **During review, ask a cold reader to restate the central idea without
   relying on the document's own terminology.** If the reader can repeat
   the labels but cannot explain the idea in different words, the draft
   has failed — the labels were memorized, not understood. This is the
   review test this framework is built around; see §"The cold-reader
   restatement test" below for how to apply it without building new
   critic infrastructure.

## Terminology exceptions (legal, patent, spec)

Point 3 above ("a term earns its place") has a documented exception for
artifact classes where the term IS the artifact's job: **exact legal,
patent, or normative-specification terminology is required, not
optional, and is never a plain-language violation on its own.**

- **`anvil:ip-uspto` / `anvil:ip-uspto-provisional`.** Claim language,
  §101/§112 doctrinal vocabulary, and defined patent terms of art
  (`comprising`, `means for`, `wherein`) are the artifact's substance —
  substituting plain language would change the claim's legal scope, not
  just its readability. The plain-language framework does not apply to
  claim text. It DOES apply to the enablement narrative and the
  background/summary sections surrounding the claims, where the same
  "explain before you name" discipline improves a reader's (including an
  examiner's) ability to follow the invention.
- **`anvil:spec`.** Normative keywords (`MUST`, `MUST NOT`, `SHOULD`,
  `MAY` per RFC 2119-style convention) and domain-specific defined terms
  a spec formally introduces are exact by design — a spec that
  paraphrases its own normative vocabulary to sound friendlier
  introduces ambiguity the artifact exists to eliminate. The framework
  applies to the prose *surrounding* normative statements (motivation,
  rationale, worked examples), not to the normative statements
  themselves.
- **Venue-required terminology (general).** Any artifact class citing a
  fixed external vocabulary it does not control — a legal filing's
  statutory language, a standards body's defined terms, a citation
  format's field names — inherits the same exception for that fixed
  vocabulary. The exception is scoped to the required term itself, not
  to the surrounding prose explaining why it applies.

The exception is narrow and per-term, not per-document: a spec or patent
draft still owes the reader plain-language framing for everything that
is NOT the exact required term. A drafter who over-applies the exception
to justify unexplained jargon elsewhere in the same document has not
used it correctly.

## The cold-reader restatement test

Point 7's review test does not require new critic infrastructure. The
memo skill already ships exactly this pattern as a first-class critic
sibling: `anvil/skills/memo/commands/memo-comprehension.md` (issue #753)
dispatches a fresh, blind sub-agent that reads only the drafted body,
answers a fixed reconstruction questionnaire in its own words, and is
scored against a `CLEAR` / `GARBLED` / `MISSING` / `HONEST-GAP` verdict
vocabulary — findings-only, non-gating, additive to the existing N-
critics-one-reviser primitive. Its question 6 ("every term you could not
define from the document alone") is a direct instance of this
framework's point 7.

`memo-comprehension` is memo-only today. Generalizing the cold-reader
pattern to other skills (a per-artifact-type questionnaire swap, per
`memo-comprehension.md`'s own "Portability note") is a **later,
separate decision** — this snippet references the worked example rather
than duplicating or generalizing it. A reviewer applying point 7 without
a dedicated critic sibling can still run the same test informally: read
the drafted body as if seeing it for the first time, and ask whether the
central idea survives being retold without the document's own coinages.

## Interaction with dim 9 (Rhetorical economy)

See `anvil/lib/snippets/rubric.md` §"Dim 9 — teaching-oriented length is
not padding" for how this framework composes with the existing
rhetorical-economy dimension: the short version is that dim 9 penalizes
padding and repetition, never patient explanation, and a critic applying
dim 9 should distinguish the two using this snippet's point 6.

## Scope note (Phase 1 of #1042)

This snippet is shared, lib-level guidance. Wiring it into any skill's
`commands/*-draft.md` / `commands/*-review.md` (so drafters and reviewers
actually load and cite it) is deliberately **out of scope here** — that
rollout is issues #1044 (paper, report, memo) and #1045 (essay, primer,
slides, deck), both of which depend on this issue. Until a skill's
commands cite this snippet by path, its existence changes no runtime
behavior — the same additive-first convention every other `anvil/lib/
snippets/` file follows.
