"""Canonical essay word count (issue #1349).

One method, one meaning for every word envelope (BRIEF ``target_length``,
the default 500-1500 envelope, the rubric's dim 9 length language).

Method (markdown -> visible prose -> tokens)
--------------------------------------------

Stripped before counting (a reader never sees them):

* YAML frontmatter, HTML comments (multi-line too), fenced code blocks
  (``` / ~~~), reference-link definitions (``[id]: url``), raw HTML tags,
  autolinks / bare URLs, and images (``![alt](src)`` -- the whole construct).
* The **title**: the first ``# `` (H1) heading line of the body. The title is
  not body prose; envelopes bound the body.

Kept:

* **Headings other than the title** -- their text is read by the reader and
  counted (``#`` markers are not words).
* **Link text** -- ``[text](url)`` counts ``text``; the URL does not. The
  collapse runs over the whole document so link text spanning a hard line
  wrap is handled.
* Inline-code contents, emphasis contents, list/blockquote text, table cells.

Tokenization: a word is a run of ASCII letters/digits with optional internal
apostrophes or hyphens (``don't``, ``well-known`` are one word each). Bare
punctuation (a standalone em dash, ``*``, ``>``, ``-`` bullets) is never a
word. This is the same tokenizer ``rhetoric_lint`` always used for its
per-1000-words density denominators; it is now defined here once.

``rhetoric_lint`` counts its already-scoped scan text (code and comments
excluded, links collapsed) with :func:`count_words`, so its denominator uses
the identical tokenizer; unlike the envelope count it keeps the title in the
scanned text, since density is a property of everything the lint scans.
"""

from __future__ import annotations

import re

__all__ = ["WORD_RE", "count_words", "visible_prose", "essay_word_count"]

WORD_RE = re.compile(r"[A-Za-z0-9]+(?:['’\-][A-Za-z0-9]+)*")

_FRONTMATTER_RE = re.compile(r"\A---[ \t]*\n.*?\n---[ \t]*(?:\n|\Z)", re.DOTALL)
_HTML_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)
_FENCE_RE = re.compile(
    r"^(?P<f>`{3,}|~{3,})[^\n]*\n.*?(?:^(?P=f)[`~]*[ \t]*$|\Z)",
    re.DOTALL | re.MULTILINE,
)
_REFDEF_RE = re.compile(r"^[ \t]{0,3}\[[^\]\n]+\]:[ \t]*\S+.*$", re.MULTILINE)
_IMAGE_RE = re.compile(r"!\[[^\]]*\]\([^)\s]*(?:\s+\"[^\"]*\")?\)")
_LINK_RE = re.compile(r"\[(?P<text>[^\]]*)\]\([^)\s]*(?:\s+\"[^\"]*\")?\)")
_REFLINK_RE = re.compile(r"\[(?P<text>[^\]]+)\]\[[^\]]*\]")
_AUTOLINK_RE = re.compile(r"<(?:https?://|mailto:)[^>\s]+>")
_BARE_URL_RE = re.compile(r"https?://\S+")
_HTML_TAG_RE = re.compile(r"</?[A-Za-z][^>\n]*>")
_H1_RE = re.compile(r"^[ \t]{0,3}#[ \t]+\S.*$", re.MULTILINE)


def count_words(text: str) -> int:
    """Count canonical tokens in text that is already visible prose."""
    return len(WORD_RE.findall(text))


def visible_prose(markdown: str, *, drop_title: bool = True) -> str:
    """Reduce markdown to the prose a reader sees (see module docstring)."""
    text = markdown.replace("\r\n", "\n")
    text = _FRONTMATTER_RE.sub("", text, count=1)
    text = _HTML_COMMENT_RE.sub("", text)
    text = _FENCE_RE.sub("", text)
    if drop_title:
        text = _H1_RE.sub("", text, count=1)
    text = _REFDEF_RE.sub("", text)
    text = _IMAGE_RE.sub("", text)
    text = _LINK_RE.sub(lambda m: m.group("text"), text)
    text = _REFLINK_RE.sub(lambda m: m.group("text"), text)
    text = _AUTOLINK_RE.sub("", text)
    text = _BARE_URL_RE.sub("", text)
    text = _HTML_TAG_RE.sub("", text)
    return text


def essay_word_count(markdown: str, *, include_title: bool = False) -> int:
    """The canonical essay word count used for every length envelope."""
    return count_words(visible_prose(markdown, drop_title=not include_title))


if __name__ == "__main__":  # pragma: no cover - tiny CLI for self-checks
    import sys

    path = sys.argv[1] if len(sys.argv) > 1 else "-"
    data = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()
    print(essay_word_count(data))
