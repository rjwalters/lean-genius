"""Unit tests for ``anvil/skills/paper/lib/bib_lint.py`` (issue #998).

Regression coverage for the reported defect: a ``paper-litsearch`` run
wrote a bare ``@article`` token inside a ``%``-prefixed "comment" block
in ``candidates.bib``. ``candidates.bib`` is never compiled by litsearch
itself, so the defect stayed latent until ``paper-draft`` merged the
entries into ``refs.bib`` and ``bibtex`` failed downstream.

These tests cover the acceptance criteria directly:

- a bare ``@<word>`` token inside a comment block is caught,
- a well-formed multi-entry ``candidates.bib`` (with interspersed
  ``%``-comments that carry no ``@``) validates cleanly — no false
  positives,
- a legitimate ``@`` inside a field value (an email-address-shaped
  string) does not false-positive,
- an entry with unbalanced braces is caught,
- ``lint_bib_file`` reads a real file on disk.

Distinct filename per the #58 packaging convention; ``__init__.py``
chain in this tests/ directory (empty, per repo convention).
"""

from __future__ import annotations

import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[4]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from anvil.skills.paper.lib.bib_lint import (  # noqa: E402
    KIND_STRAY_AT,
    KIND_UNBALANCED_BRACES,
    lint_bib_file,
    lint_bib_text,
)


# -----------------------------------------------------------------------------
# The reported failure mode: stray @article inside a comment block
# -----------------------------------------------------------------------------


def test_stray_at_inside_comment_block_is_caught():
    """Reproduces the reported shape: a discussion sentence embedded in a
    ``%``-comment block that happens to contain a bare ``@article``
    token — BibTeX has no comment syntax, so its scanner would trip on
    this exactly like an intended entry."""
    text = """\
@inproceedings{smith2024example,
  author    = {Smith, Jane and Jones, Carol},
  title     = {An Example Paper Title},
  booktitle = {Proceedings of the Example Conference},
  year      = {2024},
}

% Discussion: there's also @article-type work on noise robustness we
% might want to look at, but no BibTeX fields were supplied for it yet.

@misc{jones2023other,
  author = {Jones, Carol},
  title  = {Another Example},
  year   = {2023},
}
"""
    result = lint_bib_text(text)
    assert not result.ok
    assert len(result.issues) == 1
    issue = result.issues[0]
    assert issue.kind == KIND_STRAY_AT
    assert "@article-type" in issue.snippet or "@article" in issue.snippet
    # The stray token is on the comment line, not either real entry.
    assert issue.line == 8


def test_stray_at_bare_token_no_braces_at_all():
    """A bare '@word' with nothing brace-like anywhere on the line."""
    text = "% see also @vaswani2017 in a later pass\n"
    result = lint_bib_text(text)
    assert not result.ok
    assert result.issues[0].kind == KIND_STRAY_AT


# -----------------------------------------------------------------------------
# No false positives: well-formed candidates.bib
# -----------------------------------------------------------------------------


def test_well_formed_multi_entry_file_with_comments_validates_cleanly():
    text = """\
% Candidate bibliography for thread q3-method.
% Re-formatted from author-supplied refs/export.bib.

@inproceedings{smith2024example,
  author    = {Smith, Jane and Jones, Carol},
  title     = {An Example Paper Title},
  booktitle = {Proceedings of the Example Conference},
  year      = {2024},
}

% Second cluster: robustness literature.
@article{doe2022robust,
  author = {Doe, John},
  title  = {Robustness Under Distribution Shift},
  journal = {Journal of Examples},
  year   = {2022},
}

@misc{vaswani2017attention,
  author = {Vaswani, Ashish and others},
  title  = {Attention Is All You Need},
  year   = {2017},
}
"""
    result = lint_bib_text(text)
    assert result.ok
    assert result.issues == []


def test_at_sign_inside_field_value_is_not_flagged():
    """A legitimate '@' inside a properly braced field value (e.g. an
    email-address-shaped string in a note/author field) must not
    false-positive — it is consumed as part of the entry body."""
    text = """\
@misc{contact2024,
  author = {Smith, Jane},
  title  = {A Dataset Release},
  note   = {Contact: jane.smith@example.com for access requests.},
  year   = {2024},
}
"""
    result = lint_bib_text(text)
    assert result.ok
    assert result.issues == []


def test_empty_file_validates_cleanly():
    result = lint_bib_text("")
    assert result.ok
    assert result.issues == []


def test_single_entry_with_paren_delimiters_validates_cleanly():
    text = "@article(smith2024, author = {Smith, Jane}, year = {2024})\n"
    result = lint_bib_text(text)
    assert result.ok


# -----------------------------------------------------------------------------
# Unbalanced braces
# -----------------------------------------------------------------------------


def test_unbalanced_braces_within_entry_is_caught():
    text = """\
@article{smith2024example,
  author = {Smith, Jane},
  title  = {An Example Paper Title,
  year   = {2024},
"""
    result = lint_bib_text(text)
    assert not result.ok
    assert any(i.kind == KIND_UNBALANCED_BRACES for i in result.issues)


def test_unbalanced_braces_reports_correct_start_line():
    text = "\n\n@misc{key1, title = {Unterminated\n"
    result = lint_bib_text(text)
    assert not result.ok
    issue = result.issues[0]
    assert issue.kind == KIND_UNBALANCED_BRACES
    assert issue.line == 3


# -----------------------------------------------------------------------------
# lint_bib_file: reads a real file on disk
# -----------------------------------------------------------------------------


def test_lint_bib_file_reads_disk_file(tmp_path):
    bib_path = tmp_path / "candidates.bib"
    bib_path.write_text(
        "@misc{ok2024, author = {A}, title = {B}, year = {2024}}\n",
        encoding="utf-8",
    )
    result = lint_bib_file(bib_path)
    assert result.ok


def test_lint_bib_file_catches_stray_at_on_disk(tmp_path):
    bib_path = tmp_path / "candidates.bib"
    bib_path.write_text(
        "% see also @article-type work later\n"
        "@misc{ok2024, author = {A}, title = {B}, year = {2024}}\n",
        encoding="utf-8",
    )
    result = lint_bib_file(bib_path)
    assert not result.ok
    assert result.issues[0].kind == KIND_STRAY_AT


# -----------------------------------------------------------------------------
# to_dict() JSON shape
# -----------------------------------------------------------------------------


def test_to_dict_shape():
    result = lint_bib_text("% stray @oops here\n")
    payload = result.to_dict()
    assert payload["ok"] is False
    assert len(payload["issues"]) == 1
    issue_payload = payload["issues"][0]
    assert set(issue_payload) == {"kind", "line", "message", "snippet"}
    assert issue_payload["kind"] == KIND_STRAY_AT
