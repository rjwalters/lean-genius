"""Compile-smoke tests for ``anvil/skills/paper/templates/anvil-paper.cls`` (issue #671).

The class ships a ``numeric`` option that swaps natbib into numeric
(``[numbers,sort&compress]``) mode while keeping author-year
(``[round,sort&compress,authoryear]``) as the unchanged default. This
suite verifies, by actually compiling a minimal fixture, that:

- the default (no option) renders author-year ``(Author, Year)`` citations,
- ``[numeric]`` renders numeric ``[1]``-style citations with ``sort&compress``
  compressing a 3-key ``\\citep`` to ``[1-3]``,
- ``[numeric,anonymous]`` composes: numeric citations AND the anonymous
  author-block suppression are simultaneously in effect,
- ``plainnat`` (the baked-in default bibliographystyle) renders correctly
  under both citation modes — no bibliographystyle branching is required.

It also covers issue #1328: a ``pandoc -t latex`` ``longtable`` carrying a
``\\caption{}`` compiles under the class. That construct failed with
``No counter 'none' defined`` while the class loaded ``caption`` with no
``longtable`` in scope.

Per the repo convention for optional binaries (the ``check_*_available()``
family in ``anvil/lib/render.py``; ``shutil.which(\"pdfinfo\")`` gating in the
existing suites), every *compile* test is SKIPPED when ``pdflatex``/``bibtex``
are not on ``PATH``. There is no hard LaTeX-toolchain test dependency. The
source-level package-order assertion needs no toolchain and always runs, so
the #1328 regression stays gated even in CI (which ships no LaTeX).

Distinct filename per the #58 packaging convention; ``__init__.py`` chain
in this tests/ directory.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

_CLS = (
    Path(__file__).resolve().parents[1] / "templates" / "anvil-paper.cls"
)

_TOOLCHAIN = shutil.which("pdflatex") and shutil.which("bibtex")

#: Applied per-test rather than module-wide so the source-level assertions
#: below (which read the .cls as text and need no toolchain) still run in CI,
#: where no LaTeX distribution is installed.
_needs_latex = pytest.mark.skipif(
    not _TOOLCHAIN, reason="pdflatex/bibtex not on PATH"
)

_REFS_BIB = r"""
@article{alpha, author = {Adams, Ada}, title = {Alpha}, journal = {J}, year = {2001}}
@article{bravo, author = {Brown, Bob}, title = {Bravo}, journal = {J}, year = {2002}}
@article{charlie, author = {Carter, Cara}, title = {Charlie}, journal = {J}, year = {2003}}
"""


def _tex(options: str, body: str = "") -> str:
    opt = f"[{options}]" if options else ""
    return (
        rf"\documentclass{opt}{{anvil-paper}}"
        "\n"
        r"\title{Smoke}"
        "\n"
        r"\author{Real Author}"
        "\n"
        r"\date{2026}"
        "\n"
        r"\begin{document}"
        "\n"
        r"\maketitle"
        "\n"
        r"\begin{abstract}A.\end{abstract}"
        "\n"
        r"\section{Intro}"
        "\n"
        r"Single \citep{alpha}. Multi \citep{alpha,bravo,charlie}."
        "\n"
        f"{body}"
        "\n"
        r"\bibliographystyle{plainnat}"
        "\n"
        r"\bibliography{refs}"
        "\n"
        r"\end{document}"
        "\n"
    )


def _compile(tmp_path: Path, options: str, body: str = "") -> Path:
    """Run pdflatex/bibtex/pdflatex/pdflatex; return the produced PDF path."""
    shutil.copy(_CLS, tmp_path / "anvil-paper.cls")
    (tmp_path / "refs.bib").write_text(_REFS_BIB)
    (tmp_path / "main.tex").write_text(_tex(options, body))

    def run(cmd: list[str]) -> subprocess.CompletedProcess:
        return subprocess.run(
            cmd, cwd=tmp_path, capture_output=True, text=True, timeout=120
        )

    r1 = run(["pdflatex", "-interaction=nonstopmode", "main.tex"])
    assert r1.returncode == 0, f"first pdflatex failed ({options}):\n{r1.stdout[-2000:]}"
    run(["bibtex", "main"])
    run(["pdflatex", "-interaction=nonstopmode", "main.tex"])
    r4 = run(["pdflatex", "-interaction=nonstopmode", "main.tex"])
    assert r4.returncode == 0, f"final pdflatex failed ({options}):\n{r4.stdout[-2000:]}"

    pdf = tmp_path / "main.pdf"
    assert pdf.exists(), f"no PDF produced for options={options!r}"
    return pdf


def _text(pdf: Path) -> str:
    if not shutil.which("pdftotext"):
        pytest.skip("pdftotext not on PATH (compile succeeded; skipping render assertions)")
    out = subprocess.run(
        ["pdftotext", str(pdf), "-"], capture_output=True, text=True, timeout=60
    )
    assert out.returncode == 0
    return out.stdout


@_needs_latex
def test_default_renders_author_year(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, ""))
    assert "??" not in text, "unresolved citation markers remain"
    # Author-year: (Adams, 2001) style, no bracketed numbers on the cite.
    assert "Adams" in text and "2001" in text
    assert "Single [1]" not in text


@_needs_latex
def test_numeric_renders_bracketed_numbers(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "numeric"))
    assert "??" not in text, "unresolved citation markers remain"
    assert "Single [1]" in text
    # sort&compress collapses the 3-key cite to a range (en-dash in the PDF).
    assert ("[1–3]" in text) or ("[1-3]" in text), text


@_needs_latex
def test_numeric_anonymous_composes(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "numeric,anonymous"))
    assert "??" not in text
    # numeric citations in effect...
    assert "Single [1]" in text
    # ...AND anonymous author-block suppression in effect.
    assert "Withheld" in text
    assert "Real Author" not in text


@_needs_latex
def test_anonymous_numeric_order_independent(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "anonymous,numeric"))
    assert "Single [1]" in text
    assert "Withheld" in text
    assert "Real Author" not in text


# --------------------------------------------------------------------------
# Issue #1328: pandoc-generated longtable + \caption
#
# Verbatim output of `pandoc -t latex` (pandoc 3.x, default booktabs table
# style) for a pipe table carrying a `: caption` line. The `\caption{}`
# immediately inside the `longtable` is the construct that failed with
# "No counter 'none' defined" when the class loaded `caption` with no
# `longtable` in scope. On the class as shipped before #1328 the failure was
# even earlier — `Environment longtable undefined`, since the class never
# loaded `longtable` at all; the reported counter error is what a consumer
# saw after adding `\usepackage{longtable}` to the document preamble, which
# is too late for `caption` to install its `\LT@` hooks on older
# caption/longtable releases.
# --------------------------------------------------------------------------
_PANDOC_LONGTABLE = r"""
\begin{longtable}[]{@{}ll@{}}
\caption{A sample caption.}\tabularnewline
\toprule\noalign{}
Col A & Col B \\
\midrule\noalign{}
\endfirsthead
\toprule\noalign{}
Col A & Col B \\
\midrule\noalign{}
\endhead
\bottomrule\noalign{}
\endlastfoot
1 & 2 \\
3 & 4 \\
\end{longtable}
"""


@_needs_latex
def test_pandoc_longtable_with_caption_compiles(tmp_path: Path) -> None:
    """A pandoc `longtable` + `\\caption{}` compiles under the class (#1328)."""
    text = _text(_compile(tmp_path, "", _PANDOC_LONGTABLE))
    # The caption rendered (numbered as a table, not swallowed).
    assert "A sample caption." in text
    assert "Table 1" in text
    # ...and the table body survived the longtable page-breaking machinery.
    assert "Col A" in text and "Col B" in text


@_needs_latex
def test_pandoc_longtable_compiles_under_numeric_option(tmp_path: Path) -> None:
    """The longtable fix is independent of the citation-style option (#1328)."""
    text = _text(_compile(tmp_path, "numeric", _PANDOC_LONGTABLE))
    assert "A sample caption." in text
    assert "Single [1]" in text


# Pandoc's *wide*-table form, emitted verbatim once a table's natural width
# exceeds the line width. Beyond `longtable` it needs `array` (the `>{...}`
# column-spec prefix and `\arraybackslash`) and `calc` (the `\real{...}`
# width arithmetic) — which is why the class loads those two alongside it.
_PANDOC_LONGTABLE_WIDE = r"""
\begin{longtable}[]{@{}
  >{\raggedright\arraybackslash}p{(\linewidth - 2\tabcolsep) * \real{0.5962}}
  >{\raggedright\arraybackslash}p{(\linewidth - 2\tabcolsep) * \real{0.4038}}@{}}
\caption{Wide caption.}\tabularnewline
\toprule\noalign{}
\begin{minipage}[b]{\linewidth}\raggedright
Header one
\end{minipage} & \begin{minipage}[b]{\linewidth}\raggedright
Header two
\end{minipage} \\
\midrule\noalign{}
\endfirsthead
\toprule\noalign{}
Header one & Header two \\
\midrule\noalign{}
\endhead
\bottomrule\noalign{}
\endlastfoot
cell one & cell two \\
\end{longtable}
"""


@_needs_latex
def test_pandoc_wide_longtable_compiles(tmp_path: Path) -> None:
    """Pandoc's `p{... \\real{...}}` wide-column longtable compiles too (#1328)."""
    text = _text(_compile(tmp_path, "", _PANDOC_LONGTABLE_WIDE))
    assert "Wide caption." in text
    assert "Header one" in text and "cell two" in text


def test_class_loads_longtable_before_caption() -> None:
    """Load order is the actual fix — assert it structurally, not just by compile.

    A compile-only assertion passes on a machine where some other package in the
    chain happens to pull `longtable` in first; this pins the class's own
    ordering so a future reshuffle of the `\\RequirePackage` block cannot
    silently reintroduce #1328.
    """
    src = _CLS.read_text()
    cap = src.index(r"\RequirePackage{caption}")
    for pkg in ("longtable", "array", "calc"):
        assert (
            rf"\RequirePackage{{{pkg}}}" in src
        ), f"anvil-paper.cls must load {pkg} for pandoc longtables (#1328)"
    lt = src.index(r"\RequirePackage{longtable}")
    assert lt < cap, "anvil-paper.cls must load longtable BEFORE caption (#1328)"
