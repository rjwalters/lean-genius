"""THE regression lock for `anvil:project-scout` (issue #407) — written first.

The empirically verified hazard (curation notes, issue #407): the
foreign-grammar shape (``Whitepaper.<letter>.<N>`` families with
``.review-v2`` / ``.audit-v2`` sidecars) classifies ``PRE_283_CLASSIC``
under today's detector — the greedy ``_VERSION_DIR_RE``
(``^(?P<stem>.+)\\.(?P<num>\\d+)$``) matches ``Whitepaper.A.3`` with stem
``Whitepaper.A``. A scout that naively delegated to ``detect_shape``
would bucket this LEGACY_MIGRATABLE and recommend a migrate that mangles
the tree.

These tests lock: (1) the hazard is real (detect really does say
PRE_283_CLASSIC — if detect ever learns to refuse this shape, the
pinned premise changes and this test tells us); (2) scout buckets it
FOREIGN_GRAMMAR, NOT LEGACY_MIGRATABLE; (3) the ``why`` names the
failing predicates; (4) mixed roots bucket foreign too; (5) no command
is recommended for foreign clusters.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_scout_skill_lib import cluster, foreign, orchestrate  # noqa: E402
from _scout_fixtures import (  # noqa: E402
    build_foreign_grammar,
    build_foreign_mixed,
)

from anvil.lib.project_detect import Shape, detect_shape  # noqa: E402


class TestHazardPremise(unittest.TestCase):
    """Pin the misclassification the guard exists to intercept."""

    def test_detect_shape_misclassifies_foreign_grammar_as_classic(self) -> None:
        with TemporaryDirectory() as td:
            project = build_foreign_grammar(Path(td))
            # THE verified hazard: detect does NOT return UNKNOWN here.
            # If this ever changes, the guard's premise changed — revisit.
            self.assertIs(detect_shape(project), Shape.PRE_283_CLASSIC)


class TestForeignRegressionLock(unittest.TestCase):
    def _scout(self, root: Path):
        return orchestrate.run(root)

    def test_foreign_fixture_buckets_foreign_not_legacy(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_foreign_grammar(root)
            result = self._scout(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            # THE regression lock.
            self.assertEqual(c.bucket, cluster.BUCKET_FOREIGN_GRAMMAR)
            self.assertNotEqual(c.bucket, cluster.BUCKET_LEGACY_MIGRATABLE)
            self.assertIsNone(c.recommended_command)

    def test_why_names_failing_predicates(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_foreign_grammar(root)
            result = self._scout(root)
            c = result.classification.clusters[0]
            stems = {ff.stem for ff in c.foreign_families}
            self.assertEqual(stems, {"Whitepaper.A", "Whitepaper.B"})
            all_why = "\n".join(
                w for ff in c.foreign_families for w in ff.why
            )
            # Predicate (i): dotted stem.
            self.assertIn("contains `.`", all_why)
            # Predicate (ii): letter-series stems.
            self.assertIn("final", all_why)
            # Predicate (iii): versioned sidecar tags.
            self.assertIn("review-v2", all_why)
            self.assertIn("audit-v2", all_why)

    def test_foreign_versions_and_sidecars_inventoried(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_foreign_grammar(root)
            c = self._scout(root).classification.clusters[0]
            by_stem = {ff.stem: ff for ff in c.foreign_families}
            self.assertEqual(by_stem["Whitepaper.A"].versions, [1, 2])
            self.assertEqual(by_stem["Whitepaper.B"].versions, [1])
            self.assertIn(
                "Whitepaper.A.2.review-v2", by_stem["Whitepaper.A"].sidecars
            )
            self.assertIn(
                "Whitepaper.B.1.audit-v2", by_stem["Whitepaper.B"].sidecars
            )

    def test_mixed_root_buckets_foreign_with_per_family_detail(self) -> None:
        """Clean + foreign families under one root → FOREIGN_GRAMMAR.

        Never recommend migrate on a root the migration would partially
        mangle.
        """
        with TemporaryDirectory() as td:
            root = Path(td)
            build_foreign_mixed(root)
            result = self._scout(root)
            clusters = result.classification.clusters
            self.assertEqual(len(clusters), 1)
            c = clusters[0]
            self.assertEqual(c.bucket, cluster.BUCKET_FOREIGN_GRAMMAR)
            self.assertIsNone(c.recommended_command)
            # The clean family is named in the mixed-root note.
            notes = "\n".join(c.notes)
            self.assertIn("clean-memo", notes)
            # Only the foreign families appear in foreign_families.
            stems = {ff.stem for ff in c.foreign_families}
            self.assertEqual(stems, {"Whitepaper.A", "Whitepaper.B"})

    def test_report_only_in_markdown_and_json(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td)
            build_foreign_grammar(root)
            result = self._scout(root)
            self.assertIn("FOREIGN_GRAMMAR", result.markdown)
            self.assertIn("report-only", result.markdown)
            fg = result.data["foreign_grammar"]
            self.assertEqual(len(fg), 1)
            self.assertEqual(
                {f["stem"] for f in fg[0]["families"]},
                {"Whitepaper.A", "Whitepaper.B"},
            )
            # No migrate command anywhere in the foreign cluster entry.
            for entry in result.data["clusters"]:
                if entry["bucket"] == "FOREIGN_GRAMMAR":
                    self.assertIsNone(entry["recommended_command"])


class TestGuardPredicatesUnit(unittest.TestCase):
    """Pure-function unit coverage for the guard."""

    def test_dotted_stem_fires(self) -> None:
        found = foreign.find_foreign_families(
            [("Whitepaper.A", [1, 2], [])]
        )
        self.assertEqual(len(found), 1)
        self.assertIn("contains `.`", found[0].why[0])

    def test_numeric_tag_corner_fires(self) -> None:
        # `memo.3.1` groups as stem `memo.3` (the discover_critics skip)
        # — caught by the same dotted-stem predicate.
        found = foreign.find_foreign_families([("memo.3", [1], [])])
        self.assertEqual(len(found), 1)

    def test_versioned_sidecar_tag_fires_on_clean_stem(self) -> None:
        found = foreign.find_foreign_families(
            [("memo", [1, 2], ["memo.2.review-v2"])]
        )
        self.assertEqual(len(found), 1)
        self.assertIn("review-v2", "\n".join(found[0].why))

    def test_clean_family_does_not_fire(self) -> None:
        found = foreign.find_foreign_families(
            [
                ("memo", [1, 2, 3], ["memo.3.review"]),
                ("bispectral-imaging", [1, 3, 4], ["bispectral-imaging.3.review"]),
            ]
        )
        self.assertEqual(found, [])

    def test_canonical_audit_and_critic_tags_do_not_fire(self) -> None:
        found = foreign.find_foreign_families(
            [("memo", [1], ["memo.1.audit", "memo.1.perspective"])]
        )
        self.assertEqual(found, [])


if __name__ == "__main__":
    unittest.main()
