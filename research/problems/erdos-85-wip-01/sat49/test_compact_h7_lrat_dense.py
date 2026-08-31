import tempfile
import unittest
from pathlib import Path

from compact_h1_v2_lrat import compact_lrat as compact_dict
from compact_h7_lrat_dense import compact_lrat as compact_dense


class DenseCompactorTests(unittest.TestCase):
    def run_both(self, text: str, originals: int = 3) -> tuple[str, str]:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "raw.lrat"
            old = root / "old.lrat"
            new = root / "new.lrat"
            source.write_text(text, encoding="ascii")
            old_meta = compact_dict(source, originals, old)
            new_meta = compact_dense(source, originals, new, 1000)
            self.assertEqual(old_meta, new_meta)
            return old.read_text(), new.read_text()

    def test_byte_equivalent_with_gaps_negative_hints_and_deletions(self):
        text = "3 d 1 2 0\n10 4 0 1 2 0\n10 d 2 0\n14 0 -10 3 0\n"
        old, new = self.run_both(text)
        self.assertEqual(old, new)

    def test_byte_equivalent_empty_and_consecutive(self):
        for text in ("", "4 1 0 1 0\n5 0 4 0\n"):
            with self.subTest(text=text):
                old, new = self.run_both(text)
                self.assertEqual(old, new)

    def test_rejects_forward_unknown_and_span_cap(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "raw.lrat"
            output = root / "out.lrat"
            source.write_text("10 0 11 0\n")
            with self.assertRaisesRegex(ValueError, "forward or unknown"):
                compact_dense(source, 3, output, 100)
            source.write_text("100 0 1 0\n")
            with self.assertRaisesRegex(ValueError, "span .* exceeds cap"):
                compact_dense(source, 3, output, 10)

    def test_large_gap_crosses_extension_chunks(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "raw.lrat"
            output = root / "out.lrat"
            identifier = 2_000_010
            source.write_text(f"{identifier} 0 1 0\n")
            compact_dense(source, 3, output, 3_000_000)
            self.assertEqual(output.read_text(), "4 0 1 0\n")

    def test_malformed_input_error_parity(self):
        cases = (
            ("10 1 0 1 0\n9 0 10 0\n", "non-increasing"),
            ("10 0 1 0 0\n", "zero proof hint"),
            ("10 1 0 1 0\n10 d 0 0\n", "nonpositive deletion"),
        )
        for text, message in cases:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                source = root / "raw.lrat"
                source.write_text(text)
                for name, compactor in (("dict", compact_dict), ("dense", compact_dense)):
                    with self.subTest(compactor=name), self.assertRaisesRegex(ValueError, message):
                        compactor(source, 3, root / f"{name}.out")

    def test_rejects_non_ascii_negative_originals_and_uint32_overflow(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "raw.lrat"
            output = root / "out.lrat"
            source.write_bytes(b"10 0 1 0\n\xff")
            with self.assertRaisesRegex(ValueError, "non-ASCII"):
                compact_dense(source, 3, output)
            source.write_text("1 0 0\n")
            with self.assertRaisesRegex(ValueError, "nonnegative"):
                compact_dense(source, -1, output)
            first = (1 << 32)
            source.write_text(f"{first} 0 1 0\n")
            with self.assertRaisesRegex(ValueError, "exceeds uint32"):
                compact_dense(source, first - 1, output)

    def test_failure_preserves_destination_and_removes_temp(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "raw.lrat"
            output = root / "out.lrat"
            source.write_text("100 0 1 0\n")
            output.write_text("preserve\n")
            with self.assertRaises(ValueError):
                compact_dense(source, 3, output, 10)
            self.assertEqual(output.read_text(), "preserve\n")
            self.assertEqual(list(root.glob(".*.tmp.*")), [])


if __name__ == "__main__":
    unittest.main()
