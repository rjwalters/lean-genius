"""Unit tests for the pure document-ish classifier (issue #407, AC 8).

``classify_document`` is pure — these tests run on strings, no
filesystem. Coverage: each hard negative, each positive signal, the
soft-negative downgrade, the 0-positive NOT_DOCUMENT case, and the
README/CHANGELOG/ADR never-recommended guarantee.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import docish  # noqa: E402


PROSE = ("Plain paragraph prose with several words per line. " * 12).strip()
CTX = docish.DocContext()


def classify(filename: str, text: str, ctx=CTX):
    return docish.classify_document(filename, text, ctx)


class TestHardNegatives(unittest.TestCase):
    def test_well_known_basenames_any_case(self) -> None:
        for name in (
            "README.md",
            "readme.md",
            "Readme.md",
            "CHANGELOG.md",
            "CONTRIBUTING.md",
            "LICENSE.md",
            "CODE_OF_CONDUCT.md",
            "SECURITY.md",
            "SUPPORT.md",
            "TODO.md",
            "INSTALL.md",
            "UPGRADING.md",
            "AGENTS.md",
            "CLAUDE.md",
            "SKILL.md",
            "BRIEF.md",
            "ROADMAP.md",
            "WORK_LOG.md",
            "WORK_PLAN.md",
        ):
            with self.subTest(name=name):
                # Even with strong positive content, the hard negative wins.
                v = classify(name, "# Title\n\n" + PROSE)
                self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
                self.assertIsNone(v.confidence)

    def test_adr_convention(self) -> None:
        ctx = docish.DocContext(parent_dirname="adr")
        v = docish.classify_document(
            "0001-use-postgres.md", "# Use Postgres\n\n" + PROSE, ctx
        )
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
        self.assertIn("hard-negative:adr-convention", v.signals)
        # Same basename OUTSIDE a decisions dir is not the ADR pattern.
        v2 = classify("0001-use-postgres.md", "# Use Postgres\n\n" + PROSE)
        self.assertEqual(v2.verdict, docish.VERDICT_DOCUMENT)

    def test_doc_site_marker(self) -> None:
        ctx = docish.DocContext(in_doc_site=True)
        v = docish.classify_document("guide.md", "# Guide\n\n" + PROSE, ctx)
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
        self.assertIn("hard-negative:doc-site", v.signals)

    def test_under_dot_github(self) -> None:
        ctx = docish.DocContext(ancestor_dirnames=(".github",))
        v = docish.classify_document(
            "pull_request_template.md", "# PR\n\n" + PROSE, ctx
        )
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)

    def test_under_templates(self) -> None:
        ctx = docish.DocContext(
            parent_dirname="templates", ancestor_dirnames=("templates",)
        )
        v = docish.classify_document("memo.md", "# Memo\n\n" + PROSE, ctx)
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)

    def test_skill_frontmatter(self) -> None:
        text = (
            "---\nname: foo\nuser-invocable: true\n---\n\n# Foo\n\n" + PROSE
        )
        v = classify("foo-command.md", text)
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
        self.assertIn("hard-negative:skill-frontmatter", v.signals)


class TestPositiveSignals(unittest.TestCase):
    def test_iso_date_prefix_and_suffix(self) -> None:
        for name in (
            "2026-05-19-board-update.md",
            "board-update-2026-05-19.md",
        ):
            with self.subTest(name=name):
                v = classify(name, "Some short text.\n")
                self.assertIn("iso-date-filename", v.signals)
                self.assertEqual(v.verdict, docish.VERDICT_DOCUMENT)
                self.assertEqual(v.confidence, docish.CONFIDENCE_MEDIUM)

    def test_frontmatter_title_author_date(self) -> None:
        text = "---\ntitle: T\nauthor: A\ndate: 2026-01-01\n---\n\nbody\n"
        v = classify("analysis.md", text)
        self.assertIn("frontmatter:author,date,title", v.signals)

    def test_documentclass_tex(self) -> None:
        v = classify(
            "paper.tex", "\\documentclass{article}\n\\begin{document}\n"
        )
        self.assertIn("documentclass", v.signals)
        self.assertEqual(v.verdict, docish.VERDICT_DOCUMENT)

    def test_prose_mass(self) -> None:
        # PROSE is ~96 words; four copies clear the 300-word threshold.
        v = classify("notes.md", " ".join([PROSE] * 4))
        self.assertTrue(
            any(s.startswith("prose-mass:") for s in v.signals)
        )

    def test_single_h1_then_paragraphs(self) -> None:
        v = classify("notes.md", "# One title\n\nShort body prose.\n")
        self.assertIn("single-h1-structure", v.signals)
        # Two H1s — not the structure.
        v2 = classify("notes.md", "# One\n\ntext\n\n# Two\n\ntext\n")
        self.assertNotIn("single-h1-structure", v2.signals)

    def test_document_dirname(self) -> None:
        ctx = docish.DocContext(parent_dirname="memos")
        v = docish.classify_document("q2-update.md", "short\n", ctx)
        self.assertIn("document-dirname:memos", v.signals)

    def test_two_positives_high_confidence(self) -> None:
        v = classify(
            "2026-05-19-board-update.md", "# Board update\n\n" + PROSE
        )
        self.assertEqual(v.verdict, docish.VERDICT_DOCUMENT)
        self.assertEqual(v.confidence, docish.CONFIDENCE_HIGH)


class TestSoftNegativeAndZeroPositive(unittest.TestCase):
    def test_fence_density_downgrades_to_low(self) -> None:
        fence_block = "```python\n" + "code()\n" * 20 + "```\n"
        text = "# Snippets log 2026-05-19\n\nshort intro\n\n" + fence_block
        v = classify("2026-05-19-snippets.md", text)
        self.assertEqual(v.verdict, docish.VERDICT_DOCUMENT)
        self.assertEqual(v.confidence, docish.CONFIDENCE_LOW)
        self.assertTrue(
            any(s.startswith("soft-negative:fence-density") for s in v.signals)
        )

    def test_zero_positives_is_not_document(self) -> None:
        v = classify("misc.md", "- item one\n- item two\n")
        self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
        self.assertIsNone(v.confidence)


class TestNeverRecommended(unittest.TestCase):
    """README/CHANGELOG/ADR never carry a recommendation at any confidence
    — the verdict is NOT_DOCUMENT outright, so no confidence exists."""

    def test_readme_changelog_adr(self) -> None:
        cases = [
            ("README.md", "# R\n\n" + PROSE, CTX),
            ("CHANGELOG.md", "# C\n\n" + PROSE, CTX),
            (
                "0001-decision.md",
                "# D\n\n" + PROSE,
                docish.DocContext(parent_dirname="decisions"),
            ),
        ]
        for name, text, ctx in cases:
            with self.subTest(name=name):
                v = docish.classify_document(name, text, ctx)
                self.assertEqual(v.verdict, docish.VERDICT_NOT_DOCUMENT)
                self.assertIsNone(v.confidence)


class TestContextBuilder(unittest.TestCase):
    def test_build_doc_context_detects_mkdocs(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as td:
            root = Path(td)
            site = root / "site"
            (site / "docs").mkdir(parents=True)
            (site / "mkdocs.yml").write_text("site_name: x\n")
            f = site / "docs" / "page.md"
            f.write_text("# P\n")
            ctx = docish.build_doc_context(f, root)
            self.assertTrue(ctx.in_doc_site)
            self.assertEqual(ctx.parent_dirname, "docs")
            self.assertEqual(ctx.ancestor_dirnames, ("docs", "site"))


if __name__ == "__main__":
    unittest.main()
