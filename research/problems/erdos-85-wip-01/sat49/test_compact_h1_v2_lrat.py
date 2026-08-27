import tempfile
import unittest
from pathlib import Path

from compact_h1_v2_lrat import compact_lrat


class CompactLratTests(unittest.TestCase):
    def compact(self, text: str, originals: int = 3) -> str:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "raw.lrat"
            destination = Path(directory) / "compact.lrat"
            source.write_text(text, encoding="ascii")
            compact_lrat(source, originals, destination)
            return destination.read_text(encoding="ascii")

    def test_remaps_additions_hints_and_deletions(self):
        raw = "3 d 1 2 0\n10 4 0 1 2 0\n10 d 2 0\n14 0 -10 3 0\n"
        self.assertEqual(
            self.compact(raw),
            "4 4 0 1 2 0\n4 d 2 0\n5 0 -4 3 0\n",
        )

    def test_rejects_forward_derived_hint(self):
        with self.assertRaisesRegex(ValueError, "forward or unknown"):
            self.compact("10 0 11 0\n")

    def test_rejects_derived_identifier_in_original_domain(self):
        with self.assertRaisesRegex(ValueError, "precedes 4"):
            self.compact("3 0 1 0\n")

    def test_rejects_non_increasing_derived_identifiers(self):
        with self.assertRaisesRegex(ValueError, "non-increasing"):
            self.compact("10 1 0 1 0\n9 0 10 0\n")

    def test_rejects_zero_hint(self):
        with self.assertRaisesRegex(ValueError, "zero proof hint"):
            self.compact("10 0 1 0 0\n")

    def test_rejects_nonpositive_deletion_identifier(self):
        with self.assertRaisesRegex(ValueError, "nonpositive deletion"):
            self.compact("10 1 0 1 0\n10 d 0 0\n")

    def test_rejects_nonpositive_preamble_deletion_action(self):
        with self.assertRaisesRegex(ValueError, "nonpositive deletion"):
            self.compact("0 d 1 0\n10 0 1 0\n")

    def test_failure_does_not_replace_existing_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "raw.lrat"
            destination = Path(directory) / "compact.lrat"
            source.write_text("10 0 11 0\n", encoding="ascii")
            destination.write_text("preserve me\n", encoding="ascii")
            with self.assertRaises(ValueError):
                compact_lrat(source, 3, destination)
            self.assertEqual(destination.read_text(encoding="ascii"), "preserve me\n")
            self.assertEqual(list(Path(directory).glob(".*.tmp.*")), [])


if __name__ == "__main__":
    unittest.main()
