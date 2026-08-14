import pathlib
import tempfile
import unittest

import audit_h1_certificate_coverage as audit


class CoverageAuditTests(unittest.TestCase):
    def test_orbit_tag_matches_worker_convention(self):
        values = [0] * 24
        values[0] = 2
        items = [(audit.EDGES[0], 2)]
        import hashlib
        import json
        expected = hashlib.sha1(json.dumps(items).encode()).hexdigest()[:16]
        self.assertEqual(audit.orbit_tag(values), expected)

    def test_unknown_result_tag_is_rejected(self):
        inventory = {"0123456789abcdef": (0, (0,) * 24, 1)}
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "results.tsv"
            path.write_text("ffffffffffffffff\tLEAN_ACCEPTED\tok\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unknown orbit tag"):
                audit.read_results(path, inventory)

    def test_conflicting_status_is_rejected(self):
        tag = "0123456789abcdef"
        inventory = {tag: (0, (0,) * 24, 1)}
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "results.tsv"
            path.write_text(
                f"{tag}\tFAIL-EXC\terror\n{tag}\tLEAN_ACCEPTED\tok\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "conflicting statuses"):
                audit.read_results(path, inventory)


if __name__ == "__main__":
    unittest.main()
