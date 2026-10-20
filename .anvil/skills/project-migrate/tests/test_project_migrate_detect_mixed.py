"""Detection tests for mixed-skill and nested-but-flat shapes (issue #382).

The studio canary surfaced two shapes the memo-only detector (#297) had
never been pointed at:

- **Beacon-shaped deck** — a thread root (``<slug>/`` with BRIEF + refs +
  assets + per-thread ``.anvil.json``) sitting as a SIBLING of flat
  ``<slug>.N/`` version dirs at the project root.
- **Mixed memo + deck + proposal** — one project root with three flat
  threads in three different artifact-class grammars.

Per the #58 packaging convention this filename is unique across the
``anvil/skills/*/tests/`` tree.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import detect  # noqa: E402
from _fixtures import (  # noqa: E402
    build_beacon_shaped_deck,
    build_mixed_memo_deck_proposal,
)

Shape = detect.Shape
detect_shape = detect.detect_shape
inventory_project = detect.inventory_project


class TestBeaconShapedDeckDetection(unittest.TestCase):
    def test_classifies_pre_283_classic(self) -> None:
        """No project BRIEF + flat version dirs → PRE_283_CLASSIC."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_inventory_slug_is_stem(self) -> None:
        """The deck stem is not a skill name, so slug == stem."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            inv = inventory_project(project)
            self.assertEqual(len(inv.threads), 1)
            thread = inv.threads[0]
            self.assertEqual(thread.slug, "series-a-deck")
            self.assertEqual(thread.parent_dir, project.resolve())
            self.assertEqual(len(thread.version_dirs), 2)

    def test_inventory_records_thread_root_anvil_json(self) -> None:
        """The .anvil.json inside the sibling thread root is recorded."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            inv = inventory_project(project)
            thread = inv.threads[0]
            self.assertIsNotNone(thread.anvil_json_path)
            self.assertEqual(
                thread.anvil_json_path,
                project.resolve() / "series-a-deck" / ".anvil.json",
            )

    def test_deck_body_is_not_skill_fixed(self) -> None:
        """deck.md is observed but is NOT pre-#295 evidence."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(Path(td))
            inv = inventory_project(project)
            thread = inv.threads[0]
            self.assertIn("deck.md", thread.body_filenames)
            self.assertNotIn(
                "deck.md", detect._SKILL_FIXED_BODY_FILENAMES
            )
            self.assertIn("deck.md", detect._RETAINED_BODY_FILENAMES)

    def test_with_project_brief_classifies_post_283(self) -> None:
        """A BRIEF-bearing project with a flat deck thread → POST_283."""
        with TemporaryDirectory() as td:
            project = build_beacon_shaped_deck(
                Path(td), with_project_brief=True
            )
            self.assertEqual(
                detect_shape(project), Shape.POST_283_ANVIL_JSON
            )


class TestMixedProjectDetection(unittest.TestCase):
    def test_classifies_pre_283_classic(self) -> None:
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_inventory_finds_all_three_threads(self) -> None:
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            inv = inventory_project(project)
            slugs = sorted(t.slug for t in inv.threads)
            self.assertEqual(
                slugs, ["beacon", "gossamer-lan", "series-a-deck"]
            )

    def test_per_thread_shapes_inventoried_correctly(self) -> None:
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            inv = inventory_project(project)
            by_slug = {t.slug: t for t in inv.threads}

            # Memo thread: skill-fixed body, no thread-root .anvil.json.
            self.assertIn("memo.md", by_slug["beacon"].body_filenames)
            self.assertIsNone(by_slug["beacon"].anvil_json_path)

            # Deck thread: retained body + thread-root .anvil.json.
            self.assertIn(
                "deck.md", by_slug["series-a-deck"].body_filenames
            )
            self.assertIsNotNone(
                by_slug["series-a-deck"].anvil_json_path
            )

            # Proposal thread: proposal.tex is not a markdown body, so no
            # body filename is observed (and none is skill-fixed).
            self.assertEqual(
                [
                    b
                    for b in by_slug["gossamer-lan"].body_filenames
                    if b in detect._SKILL_FIXED_BODY_FILENAMES
                ],
                [],
            )

    def test_retained_body_surface_observes_tex_without_classify_leak(
        self,
    ) -> None:
        """Issue #386: proposal.tex appears on the dedicated
        retained-body inventory surface but stays OUT of body_filenames
        (`_classify` evidence is *.md-only by design)."""
        with TemporaryDirectory() as td:
            project = build_mixed_memo_deck_proposal(Path(td))
            inv = inventory_project(project)
            by_slug = {t.slug: t for t in inv.threads}

            self.assertIn("proposal.tex", detect._RETAINED_BODY_FILENAMES)
            self.assertEqual(
                by_slug["gossamer-lan"].retained_body_filenames,
                ["proposal.tex"],
            )
            self.assertNotIn(
                "proposal.tex", by_slug["gossamer-lan"].body_filenames
            )

            self.assertEqual(
                by_slug["series-a-deck"].retained_body_filenames,
                ["deck.md"],
            )
            # Memo threads observe no retained body.
            self.assertEqual(by_slug["beacon"].retained_body_filenames, [])

            # And classification is unchanged by the new surface.
            self.assertEqual(detect_shape(project), Shape.PRE_283_CLASSIC)

    def test_fully_migrated_mixed_tree_classifies_fully_migrated(
        self,
    ) -> None:
        """deck.md / speaker-notes.md in a nested thread do NOT block
        FULLY_MIGRATED — only skill-fixed bodies are pre-#295 evidence."""
        with TemporaryDirectory() as td:
            from _project_migrate_skill_lib import orchestrate
            project = build_mixed_memo_deck_proposal(Path(td))
            orchestrate.run(project, apply=True)
            self.assertEqual(detect_shape(project), Shape.FULLY_MIGRATED)


if __name__ == "__main__":
    unittest.main()
