"""Precision-vocabulary REMINDER tool (issue #579).

A stdlib port of the rjwalters.info ``vocab`` tool
(``scripts/vocab.mjs`` + ``words.txt``) as an anvil drafting utility.
It samples N random precision words from a word list and surfaces them
while drafting — the **generative-reminder** complement to the
judgment-side ``VOCABULARY.md`` grounding doc (issue #461 / the
phase-A #576 ``VOCABULARY.template.md``).

This is a **REMINDER tool, not an injection tool** — the single
load-bearing constraint of the whole phase
-----------------------------------------------------------------------
Human writers do not randomly sprinkle fancy words. They reach for a
specific word when it is the precise fit for a concept already being
expressed. The sample reminds the author of words they *know* but might
not reach for; a word earns its place only when it *clicks* with a
concept the draft is already trying to convey.

Consumers (and the wired essay drafter) MUST NOT auto-apply sampled
words. The discipline that keeps this safe:

- **Precision over novelty.** The word must add meaning, not variety. If
  it can be swapped back for a simpler word without losing anything,
  revert it.
- **0–2 words per 1000.** Apply sparingly; more is a red flag.
- **Respect what's working.** Do not break alliteration, parallel
  structure, or rhythm that is already doing work.
- **Gloss pattern.** When a precise term is introduced, name the concept
  then explain it ("X — a short gloss in plain language"). Use 1–2 per
  piece at most.

See ``anvil/templates/voice/VOCABULARY.template.md`` for the full
philosophy, worked examples, and the red-flags list.

Stdlib port, not a Node port
----------------------------
Mirrors the ``anvil/lib/rhetoric_lint.py`` precedent ("reimplements
draftwell's … model in pure stdlib Python, no TypeScript port"). The
source uses ``Math.random()``; this module uses the stdlib :mod:`random`
module and accepts an injectable ``rng`` so tests are deterministic
without baking nondeterminism into a replay path. **No new
dependencies** — ``random`` + a file read are sufficient.

Reproducibility caveat
----------------------
Anvil's replayable contexts forbid ``Math.random()``-style
nondeterminism. The randomness here lives inside the utility runtime (a
one-shot reminder a human reads while drafting). Sampled words MUST
NEVER be written into ``_progress.json``, the body, or any artifact that
must replay deterministically — the reminder is surfaced, consulted, and
discarded.

Source resolution
-----------------
The declared ``voice.vocabulary`` entry resolves to a PROSE markdown doc
(``VOCABULARY.md``), not a newline-delimited word list. So "draw from
the consumer's declared vocabulary source" cannot mean "read the
vocabulary doc as a word list." :func:`resolve_word_list` reuses
:func:`anvil.lib.project_brief.resolve_voice_docs` and looks for a
**sibling word-list file** next to the resolved ``vocabulary`` doc — by
convention ``<stem>.words.txt`` (e.g. ``VOCABULARY.words.txt`` next to
``VOCABULARY.md``). This needs no schema change. When no sibling list is
found (or no ``voice:`` block is declared), it falls back to the
anvil-shipped default at ``anvil/templates/voice/vocab.words.txt`` — a
small curated set. A consumer points the tool at their own larger list
simply by dropping a sibling ``<stem>.words.txt``.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path
from typing import List, Optional

# Default sample size — matches the source tool's default of 20.
DEFAULT_SAMPLE_COUNT = 20

# Sibling-file convention: the word list lives next to the declared
# vocabulary doc as ``<stem>.words.txt`` (e.g. ``VOCABULARY.words.txt``
# beside ``VOCABULARY.md``). Schema-free — no new voice sub-key.
WORDS_SIBLING_SUFFIX = ".words.txt"

# The anvil-shipped default word list (small curated cross-domain set).
# Lives under the voice templates so it ships and scaffolds with the
# other voice-grounding starter files.
DEFAULT_WORD_LIST_PATH = (
    Path(__file__).resolve().parent.parent
    / "templates"
    / "voice"
    / "vocab.words.txt"
)


def parse_word_list(text: str) -> List[str]:
    """Parse word-list text into a de-duplicated, order-preserving list.

    One word per line. Blank lines and ``#``-prefixed comment lines are
    dropped; surrounding whitespace is trimmed. Duplicates are removed
    (first occurrence wins) so a word cannot be over-represented in the
    sample. Mirrors ``vocab.mjs``'s trim-and-drop-blanks loader, plus
    comment support so the shipped default can carry a header.
    """
    seen: set = set()
    words: List[str] = []
    for raw in text.splitlines():
        word = raw.strip()
        if not word or word.startswith("#"):
            continue
        if word in seen:
            continue
        seen.add(word)
        words.append(word)
    return words


def load_word_list(path: Path) -> List[str]:
    """Read and parse a word-list file. Returns ``[]`` if it cannot be read.

    Never raises on a missing / unreadable file — the source-resolution
    helper falls back to the shipped default, mirroring the never-raise
    posture of ``resolve_voice_docs``.
    """
    try:
        text = Path(path).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []
    return parse_word_list(text)


def sample_reminder_words(
    words: List[str],
    n: int = DEFAULT_SAMPLE_COUNT,
    *,
    rng: Optional[random.Random] = None,
) -> List[str]:
    """Sample ``n`` distinct reminder words from ``words``.

    The pure core of the tool — a REMINDER sampler, never an injector.

    Parameters
    ----------
    words
        The source word list. Treated as a pool of distinct candidates;
        callers should pass the output of :func:`parse_word_list` /
        :func:`load_word_list` (which already de-duplicates).
    n
        How many words to sample. Clamped to ``len(words)`` — when
        ``n >= len(words)`` the whole list is returned (shuffled), never
        raising. ``n <= 0`` returns ``[]``.
    rng
        Optional injectable :class:`random.Random` for deterministic
        sampling (tests pass a seeded instance). When ``None`` a fresh
        module-default RNG is used so each run differs — exactly the
        one-shot, non-replayable nondeterminism the source tool relies
        on. NEVER persist the result into a replayable artifact.

    Returns
    -------
    List[str]
        ``min(n, len(words))`` distinct words, in random order. No
        duplicates (the pool is distinct and ``random.sample`` draws
        without replacement).
    """
    if n <= 0 or not words:
        return []
    generator = rng if rng is not None else random.Random()
    k = min(n, len(words))
    return generator.sample(list(words), k)


def resolve_word_list(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> List[str]:
    """Resolve the word list for a project, with the documented fallback.

    Source order:

    1. **A sibling word-list file** next to the resolved
       ``voice.vocabulary`` doc — ``<stem>.words.txt`` (e.g.
       ``VOCABULARY.words.txt`` beside ``VOCABULARY.md``). Reuses
       :func:`anvil.lib.project_brief.resolve_voice_docs` to find the
       declared/resolved vocabulary doc; does NOT re-implement the
       project-root-then-consumer-root walk and does NOT read the prose
       ``VOCABULARY.md`` itself as a word list (it is guidance, not a
       list).
    2. **The anvil-shipped default** at
       :data:`DEFAULT_WORD_LIST_PATH` — a small curated set, so the tool
       works out of the box.

    Never raises: a missing BRIEF, an inactive ``voice:`` tier, a
    declared-but-missing vocabulary doc, or an absent sibling list all
    fall through to the default. (Mirrors ``resolve_voice_docs``'s
    never-raise-on-absence posture.)
    """
    sibling = _resolve_sibling_word_list_path(project_dir, consumer_root)
    if sibling is not None:
        words = load_word_list(sibling)
        if words:
            return words
    return load_word_list(DEFAULT_WORD_LIST_PATH)


def _resolve_sibling_word_list_path(
    project_dir: Path,
    consumer_root: Optional[Path] = None,
) -> Optional[Path]:
    """Return the existing sibling ``<stem>.words.txt`` path, or ``None``.

    Locates the resolved ``voice.vocabulary`` doc via
    ``resolve_voice_docs`` and checks for a sibling word list. Returns
    ``None`` when the voice tier is inactive, no vocabulary doc is
    declared, the doc is declared-but-missing (no resolved path to take a
    sibling of), or the sibling file does not exist.
    """
    # Imported lazily so importing this module never forces the (heavier)
    # project_brief / pydantic import chain on consumers that only want
    # the pure sampler core.
    from anvil.lib.project_brief import resolve_voice_docs

    resolved = resolve_voice_docs(project_dir, consumer_root=consumer_root)
    for entry in resolved:
        if entry.kind != "vocabulary" or entry.missing:
            continue
        for path_str in entry.paths:
            doc = Path(path_str)
            sibling = doc.with_name(doc.stem + WORDS_SIBLING_SUFFIX)
            if sibling.is_file():
                return sibling
    return None


# ---------------------------------------------------------------------------
# CLI entry-point — mirrors vocab.mjs ergonomics: `python -m
# anvil.lib.vocab_reminder [count]`. A human runs it a few times while
# drafting; the framing restates the reminder-not-injector rule so the
# output can't be mistaken for an injection list.
# ---------------------------------------------------------------------------


def _build_cli_parser():
    import argparse

    p = argparse.ArgumentParser(
        prog="python -m anvil.lib.vocab_reminder",
        description=(
            "Surface N random precision words as a drafting REMINDER (NOT "
            "an injector). Run it a few times while reviewing a draft; "
            "apply a word ONLY when it clicks with a concept you are "
            "already expressing. Precision over novelty; 0-2 per 1000."
        ),
    )
    p.add_argument(
        "count",
        nargs="?",
        type=int,
        default=DEFAULT_SAMPLE_COUNT,
        help=f"How many words to surface (default {DEFAULT_SAMPLE_COUNT}).",
    )
    p.add_argument(
        "--project-dir",
        default=".",
        help=(
            "Project root to resolve the word list from (sibling "
            "<stem>.words.txt next to the declared voice.vocabulary doc, "
            "else the anvil default). Defaults to the current directory."
        ),
    )
    p.add_argument(
        "--seed",
        type=int,
        default=None,
        help=(
            "Optional RNG seed for a reproducible sample (testing / "
            "demos). Omit for a fresh sample each run."
        ),
    )
    return p


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. Returns the process exit code.

    Exit codes:
    - ``0``: a sample was surfaced.
    - ``1``: no words available (empty resolved list).
    """
    parser = _build_cli_parser()
    args = parser.parse_args(argv)

    words = resolve_word_list(Path(args.project_dir))
    rng = random.Random(args.seed) if args.seed is not None else None
    sample = sample_reminder_words(words, args.count, rng=rng)

    if not sample:
        print("no words available to sample", file=sys.stderr)
        return 1

    bar = "=" * 59
    rule = "-" * 59
    print(f"\n{bar}")
    print(f"  VOCABULARY REMINDER: {len(sample)} words from {len(words)} total")
    print(bar + "\n")
    for i, word in enumerate(sample, start=1):
        print(f"  {str(i).rjust(2)}.  {word}")
    print(f"\n{rule}")
    print("  REMINDER, not injector. Apply a word ONLY when it clicks with")
    print("  a concept you are already expressing. Precision over novelty;")
    print("  0-2 per 1000; revert if a simpler word loses nothing.")
    print(rule + "\n")
    return 0


__all__ = [
    "DEFAULT_SAMPLE_COUNT",
    "WORDS_SIBLING_SUFFIX",
    "DEFAULT_WORD_LIST_PATH",
    "parse_word_list",
    "load_word_list",
    "sample_reminder_words",
    "resolve_word_list",
    "main",
]


if __name__ == "__main__":
    raise SystemExit(main())
