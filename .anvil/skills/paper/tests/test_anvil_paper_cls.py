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

Per the repo convention for optional binaries (the ``check_*_available()``
family in ``anvil/lib/render.py``; ``shutil.which(\"pdfinfo\")`` gating in the
existing suites), the whole module is SKIPPED when ``pdflatex``/``bibtex``
are not on ``PATH``. There is no hard LaTeX-toolchain test dependency.

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

pytestmark = pytest.mark.skipif(
    not _TOOLCHAIN, reason="pdflatex/bibtex not on PATH"
)

_REFS_BIB = r"""
@article{alpha, author = {Adams, Ada}, title = {Alpha}, journal = {J}, year = {2001}}
@article{bravo, author = {Brown, Bob}, title = {Bravo}, journal = {J}, year = {2002}}
@article{charlie, author = {Carter, Cara}, title = {Charlie}, journal = {J}, year = {2003}}
"""


def _tex(options: str) -> str:
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
        r"\bibliographystyle{plainnat}"
        "\n"
        r"\bibliography{refs}"
        "\n"
        r"\end{document}"
        "\n"
    )


def _compile(tmp_path: Path, options: str) -> Path:
    """Run pdflatex/bibtex/pdflatex/pdflatex; return the produced PDF path."""
    shutil.copy(_CLS, tmp_path / "anvil-paper.cls")
    (tmp_path / "refs.bib").write_text(_REFS_BIB)
    (tmp_path / "main.tex").write_text(_tex(options))

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


def test_default_renders_author_year(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, ""))
    assert "??" not in text, "unresolved citation markers remain"
    # Author-year: (Adams, 2001) style, no bracketed numbers on the cite.
    assert "Adams" in text and "2001" in text
    assert "Single [1]" not in text


def test_numeric_renders_bracketed_numbers(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "numeric"))
    assert "??" not in text, "unresolved citation markers remain"
    assert "Single [1]" in text
    # sort&compress collapses the 3-key cite to a range (en-dash in the PDF).
    assert ("[1–3]" in text) or ("[1-3]" in text), text


def test_numeric_anonymous_composes(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "numeric,anonymous"))
    assert "??" not in text
    # numeric citations in effect...
    assert "Single [1]" in text
    # ...AND anonymous author-block suppression in effect.
    assert "Withheld" in text
    assert "Real Author" not in text


def test_anonymous_numeric_order_independent(tmp_path: Path) -> None:
    text = _text(_compile(tmp_path, "anonymous,numeric"))
    assert "Single [1]" in text
    assert "Withheld" in text
    assert "Real Author" not in text
