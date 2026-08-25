#!/usr/bin/env python3

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path


HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "filter_h1_all_even_capacity_inventory.py"


class AllEvenCapacityInventoryTest(unittest.TestCase):
    def test_authoritative_inventory_and_jobs(self) -> None:
        with tempfile.TemporaryDirectory() as raw_tmp:
            tmp = Path(raw_tmp)
            manifest = tmp / "manifest.tsv"
            jobs = tmp / "jobs.tsv"
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    "--summary-only",
                    "--manifest-output",
                    str(manifest),
                    "--lean-exact-jobs-output",
                    str(jobs),
                ],
                check=True,
                text=True,
                capture_output=True,
            )
            self.assertIn("counts=[609, 16, 1587, 6, 285] total=2503", result.stdout)

            manifest_rows = [line.split("\t") for line in manifest.read_text().splitlines()]
            job_rows = [line.split("\t") for line in jobs.read_text().splitlines()]
            self.assertEqual(len(manifest_rows), 2503)
            self.assertEqual(len(job_rows), 2503)
            self.assertEqual(Counter(int(row[1]) for row in job_rows), {
                0: 609, 1: 16, 2: 1587, 3: 6, 4: 285,
            })
            self.assertTrue(all(len(row) == 7 for row in job_rows))
            self.assertEqual(
                [row[0] for row in manifest_rows],
                [row[0] for row in job_rows],
            )
            self.assertEqual(len({row[0] for row in job_rows}), 2503)

            for row in job_rows:
                table_path = Path(row[4])
                self.assertTrue(table_path.is_file())
                self.assertEqual(row[5:], ["", ""])


if __name__ == "__main__":
    unittest.main()
