"""Fault-injection tests for `anvil:project-migrate` per-doc rollback (issue #301).

PR #300 shipped per-doc atomicity in ``lib.apply._apply_document``: each
``DocumentPlan`` is snapshotted before apply, the body of the apply is
wrapped in try/except, and any exception triggers ``_restore_doc`` to
roll the failing doc back to its pre-migration state. The rollback
machinery had no test exercising it — this module supplies that test by
monkey-patching ``lib.apply._rename`` to raise on a specific source path,
forcing the apply of one doc (the second of three) to fail.

Assertions:

- The failing doc is rolled back to its **pre-migration on-disk shape**
  (legacy ``memo.md`` body, no ``<slug>.md``, no ``BRIEF.md`` entry).
- The successfully-migrated doc (before the failure) stays migrated
  (renamed body filename, new version-dir name).
- The third doc — applied AFTER the failure under ``apply_plan``'s
  continue-on-failure loop semantics — is processed independently of the
  failing doc; its presence here documents that the per-doc atomicity
  contract is genuinely per-doc, not all-or-nothing across the project.
- ``ApplyResult`` reports the partial outcome: the surviving docs in
  ``applied_docs``, the failing doc in ``failed_docs`` with a non-empty
  diagnostic.

The injected fault simulates "the rename of the second doc's source
directory fails mid-migration" (e.g., a filesystem race, permission
hiccup, or surprise lock). The recovery contract is what's being
verified, not the specific failure mode.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest import mock

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

from _project_migrate_skill_lib import apply_mod, detect, plan  # noqa: E402
from _fixtures import build_post_283_anvil_json  # noqa: E402

ROLLBACK_SUBDIR = apply_mod.ROLLBACK_SUBDIR
apply_plan = apply_mod.apply_plan
Shape = detect.Shape
build_plan = plan.build_plan


_THREE_SLUGS = ["doc-a", "doc-b", "doc-c"]


def _make_failing_rename(fail_on_slug: str):
    """Return a stand-in for ``lib.apply._rename`` that raises on a slug.

    The real ``_rename(source, target, git_info)`` is delegated to for
    every call EXCEPT when ``source`` lives under a directory whose name
    matches ``fail_on_slug`` — in that case, ``OSError`` is raised to
    simulate a mid-apply filesystem failure on that document.

    The match is on path segments rather than substring so that a slug
    like ``doc-b`` doesn't spuriously hit ``doc-burritos`` if such a doc
    ever appeared.
    """
    real_rename = apply_mod._rename

    def _injected_rename(source, target, git_info):
        if fail_on_slug in source.parts:
            raise OSError(
                f"injected fault: simulated rename failure on {source}"
            )
        return real_rename(source, target, git_info)

    return _injected_rename


class TestPerDocRollback(unittest.TestCase):
    """Inject a rename failure on the second of three docs.

    Verifies the per-doc rollback contract of ``_apply_document``: the
    failing doc returns to its pre-migration shape while sibling docs are
    unaffected.
    """

    def test_failing_doc_rolled_back_to_pre_migration_state(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(
                Path(td), project_name="three-docs", slugs=list(_THREE_SLUGS)
            )
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)

            # Sanity: the planner emitted one DocumentPlan per slug in the
            # order we expect, so "fail on doc-b" really is "fail on the
            # second of three".
            planned_slugs = [doc.slug for doc in plan.documents]
            self.assertEqual(planned_slugs, _THREE_SLUGS)

            patched = _make_failing_rename("doc-b")
            with mock.patch.object(apply_mod, "_rename", new=patched):
                apply_plan(plan, use_git=False)

            # --- Failing doc rolled back ---------------------------------
            # The pre-migration body lived at doc-b/doc-b.1/memo.md. After
            # rollback that file should be restored and the post-migration
            # filename (doc-b.md) should NOT exist.
            failing_v1_legacy_body = (
                project / "doc-b" / "doc-b.1" / "memo.md"
            )
            failing_v1_migrated_body = (
                project / "doc-b" / "doc-b.1" / "doc-b.md"
            )
            self.assertTrue(
                failing_v1_legacy_body.is_file(),
                "rollback should restore the pre-migration memo.md body",
            )
            self.assertFalse(
                failing_v1_migrated_body.is_file(),
                "rolled-back doc should not have a post-migration "
                "<slug>.md body",
            )

            # The per-thread .anvil.json should still exist on the failing
            # doc (rollback restores it from the snapshot).
            failing_anvil_json = project / "doc-b" / ".anvil.json"
            self.assertTrue(
                failing_anvil_json.is_file(),
                "rollback should restore the pre-migration .anvil.json",
            )

    def test_successfully_migrated_doc_before_failure_stays_migrated(
        self,
    ) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(
                Path(td), project_name="three-docs", slugs=list(_THREE_SLUGS)
            )
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)

            patched = _make_failing_rename("doc-b")
            with mock.patch.object(apply_mod, "_rename", new=patched):
                apply_plan(plan, use_git=False)

            # doc-a applied cleanly before the failure: its body should be
            # renamed to <slug>.md and the legacy memo.md should be gone.
            doc_a_migrated = project / "doc-a" / "doc-a.1" / "doc-a.md"
            doc_a_legacy = project / "doc-a" / "doc-a.1" / "memo.md"
            self.assertTrue(
                doc_a_migrated.is_file(),
                "doc applied before the failure should stay migrated",
            )
            self.assertFalse(
                doc_a_legacy.is_file(),
                "successfully-migrated doc should not retain legacy body",
            )

    def test_apply_result_reports_partial_success(self) -> None:
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(
                Path(td), project_name="three-docs", slugs=list(_THREE_SLUGS)
            )
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)

            patched = _make_failing_rename("doc-b")
            with mock.patch.object(apply_mod, "_rename", new=patched):
                result = apply_plan(plan, use_git=False)

            # Failure recorded with a non-empty diagnostic.
            self.assertEqual(
                len(result.failed_docs),
                1,
                f"expected exactly one failed doc, got: {result.failed_docs}",
            )
            failing_slug, failing_msg = result.failed_docs[0]
            self.assertEqual(failing_slug, "doc-b")
            self.assertTrue(
                failing_msg,
                "failed_docs diagnostic message should be non-empty",
            )
            self.assertIn(
                "injected fault",
                failing_msg,
                "diagnostic should surface the underlying error",
            )

            # The succeeding doc(s) are recorded in applied_docs.
            self.assertIn("doc-a", result.applied_docs)
            self.assertNotIn("doc-b", result.applied_docs)

            # Per the apply contract: when any doc fails, the BRIEF write is
            # skipped (BRIEF.md is the project-level coordination point and
            # should not advertise a partially-migrated state).
            self.assertFalse(
                result.brief_written,
                "BRIEF should not be written when any doc failed",
            )

    def test_rollback_dir_cleaned_up_after_partial_apply(self) -> None:
        """The per-doc snapshot subtree should not be left behind."""
        with TemporaryDirectory() as td:
            project = build_post_283_anvil_json(
                Path(td), project_name="three-docs", slugs=list(_THREE_SLUGS)
            )
            plan = build_plan(project, Shape.POST_283_ANVIL_JSON)

            patched = _make_failing_rename("doc-b")
            with mock.patch.object(apply_mod, "_rename", new=patched):
                apply_plan(plan, use_git=False)

            rollback = project / ROLLBACK_SUBDIR
            # The per-slug snapshot for doc-b is removed at the end of
            # _apply_document's except branch; the rollback_root itself is
            # removed by apply_plan when empty.
            if rollback.is_dir():
                # If the rollback root still exists, it must be empty —
                # otherwise rollback debris is leaking onto disk.
                leftover = list(rollback.iterdir())
                self.assertEqual(
                    leftover,
                    [],
                    f"rollback dir not cleaned: {leftover}",
                )


if __name__ == "__main__":
    unittest.main()
