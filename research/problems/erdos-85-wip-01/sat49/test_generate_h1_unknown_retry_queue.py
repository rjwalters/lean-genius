#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path

from generate_h1_unknown_retry_queue import read_jobs, select_unknowns


HEADER = (
    "tag\tprofile\tfamily\tlocal_index\tstatus\tcertified_s3\t"
    "fleet_claim\tfleet_verdict\n"
)


class UnknownRetryQueueTest(unittest.TestCase):
    def test_selects_only_exact_bounded_unknown_contract(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jobs = root / "jobs.tsv"
            jobs.write_text(
                "0000000000000001\t0\tBBBB\t7\n"
                "0000000000000002\t1\tABBB\t9\n"
                "0000000000000003\t2\tAABB\t11\n"
            )
            coverage = root / "coverage.tsv"
            coverage.write_text(
                HEADER
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t1\tUNKNOWN\n"
                + "0000000000000002\t1\tABBB\t9\tcertified-in-S3\t1\t1\tUNSAT\n"
                + "0000000000000003\t2\tAABB\t11\tpending\t0\t0\t\n"
            )
            self.assertEqual(
                select_unknowns(coverage, read_jobs(jobs)),
                ["0000000000000001\t0\tBBBB\t7"],
            )

    def test_identity_mismatch_and_universe_gap_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jobs = root / "jobs.tsv"
            jobs.write_text("0000000000000001\t0\tBBBB\t7\n")
            coverage = root / "coverage.tsv"
            coverage.write_text(
                HEADER + "0000000000000001\t0\tBBBB\t8\tpending\t0\t1\tUNKNOWN\n"
            )
            with self.assertRaisesRegex(ValueError, "identity mismatch"):
                select_unknowns(coverage, read_jobs(jobs))
            coverage.write_text(HEADER)
            with self.assertRaisesRegex(ValueError, "absent from coverage"):
                select_unknowns(coverage, read_jobs(jobs))

    def test_nonqueue_coverage_rows_are_allowed_but_retry_rows_are_not(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jobs = root / "jobs.tsv"
            jobs.write_text("0000000000000001\t0\tBBBB\t7\n")
            coverage = root / "coverage.tsv"
            coverage.write_text(
                HEADER
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t0\t\n"
                + "0000000000000002\t1\tABBB\t9\tcertified-in-S3\t1\t0\t\n"
            )
            self.assertEqual(select_unknowns(coverage, read_jobs(jobs)), [])
            coverage.write_text(
                HEADER
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t0\t\n"
                + "0000000000000002\t1\tABBB\t9\tpending\t0\t1\tUNKNOWN\n"
            )
            with self.assertRaisesRegex(ValueError, "retry tag absent from jobs"):
                select_unknowns(coverage, read_jobs(jobs))


if __name__ == "__main__":
    unittest.main()
