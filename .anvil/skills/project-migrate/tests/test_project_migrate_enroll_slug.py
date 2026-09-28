"""Slug-derivation unit tests for enrollment (issue #406).

Covers ``derive_slug`` (date prefix/suffix stripping + capture,
sanitization, empty-result hard error) and ``validate_explicit_slug``
(canonical-form rejection — never silent re-sanitization).
"""

from __future__ import annotations

import pytest

from _project_migrate_skill_lib import enroll

derive_slug = enroll.derive_slug
validate_explicit_slug = enroll.validate_explicit_slug
EnrollError = enroll.EnrollError


class TestDeriveSlug:
    def test_plain_stem(self):
        assert derive_slug("board-update") == ("board-update", None)

    def test_date_prefix_stripped_and_captured(self):
        assert derive_slug("2026-05-19-board-update") == (
            "board-update",
            "2026-05-19",
        )

    def test_date_suffix_stripped_and_captured(self):
        assert derive_slug("draft-response-2026-05-19") == (
            "draft-response",
            "2026-05-19",
        )

    def test_date_prefix_wins_when_both_present(self):
        slug, date = derive_slug("2026-05-19-topic-2026-05-20")
        assert slug == "topic"
        assert date == "2026-05-19"

    def test_underscore_and_space_separators(self):
        assert derive_slug("2026-05-19_board update") == (
            "board-update",
            "2026-05-19",
        )

    def test_lowercased_and_collapsed(self):
        slug, date = derive_slug("Counterparty  Analysis (v0)")
        assert slug == "counterparty-analysis-v0"
        assert date is None

    def test_leading_trailing_hyphens_trimmed(self):
        assert derive_slug("--topic--") == ("topic", None)

    def test_date_only_stem_is_its_own_slug(self):
        # No separator → neither prefix nor suffix pattern fires; the
        # date itself is a canonical slug.
        assert derive_slug("2026-05-19") == ("2026-05-19", None)

    def test_empty_after_stripping_is_hard_error(self):
        with pytest.raises(EnrollError, match="--slug"):
            derive_slug("2026-05-19-")

    def test_nonalnum_only_stem_is_hard_error(self):
        with pytest.raises(EnrollError, match="--slug"):
            derive_slug("***")


class TestValidateExplicitSlug:
    @pytest.mark.parametrize(
        "slug", ["topic-a", "a", "topic-2", "2026-05-19"]
    )
    def test_canonical_accepted(self, slug):
        assert validate_explicit_slug(slug) == slug

    @pytest.mark.parametrize(
        "slug",
        [
            "Topic-A",  # uppercase
            "-topic",  # leading hyphen
            "topic a",  # space
            "topic/a",  # path separator
            "topic_a",  # underscore
            "",  # empty
        ],
    )
    def test_non_canonical_rejected_not_resanitized(self, slug):
        with pytest.raises(EnrollError, match="not canonical"):
            validate_explicit_slug(slug)
