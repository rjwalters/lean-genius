"""Numeral-multiset invariant for reorder-style revisions (issue #1400).

When a reviser reorders or rewords sections, every number in the paper
should survive unchanged: the *multiset* of numerals in version N+1 should
equal the multiset in version N, regardless of where each one moved. A text
diff is too noisy for that (a reorder rewrites most lines); a multiset
compares counts only, so it is order-insensitive.

This is the deterministic half of #1400. The other half, the "reworded
caveats" list, stays reviser-side: see ``paper-revise.md`` step 10b for why
regex detection of changed quantifiers/connectives was left to the LLM.

What is counted
---------------

- Numerals in prose and in math (``$...$``, ``\\[...\\]``, ``equation`` and
  friends) unless ``strip_math=True``. Counting math keeps pinned constants
  such as ``$p < 0.05$`` under the invariant; stripping is for papers whose
  math is renumbered or rewritten wholesale.
- LaTeX comments (unescaped ``%`` to end of line) are dropped on both sides.
- Arguments of reference-like macros (``\\label``, ``\\ref``, ``\\eqref``,
  ``\\cite*``, ``\\input``, ``\\include*``, ``\\includegraphics``, ``\\url``,
  ``\\href`` target) are dropped, so ``\\label{tab:2}`` or ``\\cite{li2020}``
  moving or being renamed is not drift.
- Thousands separators are normalized (``1,000`` == ``1000``). Decimals and
  percents keep their digits (``87.3`` stays ``87.3``).

Public API: ``numeral_multiset(text)``, ``diff_multisets(old, new)``,
``MultisetDiff`` and the CLI ``python -m anvil.lib.numeral_multiset OLD NEW``
(exit 0 = identical multisets, 1 = drift, 2 = unreadable input).
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")
_REF_ARG_RE = re.compile(
    r"\\(?:label|ref|eqref|autoref|cref|Cref|pageref|nameref|cite[a-zA-Z]*|"
    r"input|include|includegraphics|bibliography|bibliographystyle|url|"
    r"usepackage|documentclass)\*?(?:\[[^\]]*\])*\{[^}]*\}"
)
_HREF_TARGET_RE = re.compile(r"\\href\{[^}]*\}")
_MATH_RES = (
    re.compile(r"\$\$.*?\$\$", re.DOTALL),
    re.compile(r"(?<!\\)\$.*?(?<!\\)\$", re.DOTALL),
    re.compile(r"\\\[.*?\\\]", re.DOTALL),
    re.compile(r"\\\(.*?\\\)", re.DOTALL),
    re.compile(
        r"\\begin\{(equation|align|gather|multline|eqnarray|displaymath)\*?\}"
        r".*?\\end\{\1\*?\}",
        re.DOTALL,
    ),
)
# Digits with optional thousands groups and decimals: 1,234.5  87.3  42
_NUMERAL_RE = re.compile(r"(?<![A-Za-z\d])\d{1,3}(?:,\d{3})+(?:\.\d+)?|\d+(?:\.\d+)?")


def _normalize(numeral: str) -> str:
    return numeral.replace(",", "")


def numeral_multiset(text: str, *, strip_math: bool = False) -> Counter[str]:
    """Return the multiset of numerals in LaTeX/markdown ``text``."""
    text = _COMMENT_RE.sub("", text)
    text = _REF_ARG_RE.sub("", text)
    text = _HREF_TARGET_RE.sub("", text)
    if strip_math:
        for rx in _MATH_RES:
            text = rx.sub(" ", text)
    return Counter(_normalize(m.group(0)) for m in _NUMERAL_RE.finditer(text))


@dataclass
class MultisetDiff:
    """Order-insensitive numeral delta between two versions."""

    added: dict[str, int] = field(default_factory=dict)  # in new, not old (count excess)
    removed: dict[str, int] = field(default_factory=dict)  # in old, not new

    def passed(self) -> bool:
        return not self.added and not self.removed

    def to_markdown(self) -> str:
        if self.passed():
            return "numeral multiset: identical (order-insensitive)"
        lines = ["numeral multiset: DRIFT"]
        for label, delta in (("removed", self.removed), ("added", self.added)):
            for tok, n in sorted(delta.items()):
                lines.append(f"- {label}: `{tok}` x{n}")
        return "\n".join(lines)


def diff_multisets(old: str, new: str, *, strip_math: bool = False) -> MultisetDiff:
    """Compare numeral multisets of ``old`` and ``new``."""
    a = numeral_multiset(old, strip_math=strip_math)
    b = numeral_multiset(new, strip_math=strip_math)
    return MultisetDiff(added=dict(b - a), removed=dict(a - b))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("old", type=Path)
    ap.add_argument("new", type=Path)
    ap.add_argument("--strip-math", action="store_true")
    args = ap.parse_args(argv)
    try:
        old = args.old.read_text(encoding="utf-8")
        new = args.new.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    d = diff_multisets(old, new, strip_math=args.strip_math)
    print(d.to_markdown())
    return 0 if d.passed() else 1


if __name__ == "__main__":
    raise SystemExit(main())
