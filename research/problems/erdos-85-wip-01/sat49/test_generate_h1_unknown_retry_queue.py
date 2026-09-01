#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import generate_h1_unknown_retry_queue as queue_module
from generate_h1_unknown_retry_queue import (
    V2_CLAIM_PREFIX,
    atomic_write,
    read_jobs,
    read_orphan_tags_bytes,
    select_unknowns,
    select_unknowns_bytes,
)


HEADER = (
    "tag\tprofile\tfamily\tlocal_index\tstatus\tcertified_s3\t"
    "fleet_v2_claim\tfleet_v2_verdict\tfleet_v3_claim\tfleet_v3_verdict\n"
)


class UnknownRetryQueueTest(unittest.TestCase):
    def test_output_publication_is_create_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "queue.tsv"
            atomic_write(output, b"first\n")
            with self.assertRaises(FileExistsError):
                atomic_write(output, b"replacement\n")
            self.assertEqual(output.read_bytes(), b"first\n")

    def test_input_change_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "jobs.tsv"
            source.write_bytes(b"snapshot")
            first = source.stat()
            changed = mock.Mock(**{
                name: getattr(first, name)
                for name in ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_mode")
            })
            changed.st_mtime_ns += 1
            with mock.patch.object(queue_module.os, "fstat", side_effect=[first, changed]):
                with self.assertRaisesRegex(ValueError, "changed while being read"):
                    queue_module.stable_read(source)

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
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t1\tUNKNOWN\t0\t\n"
                + "0000000000000002\t1\tABBB\t9\tcertified-in-S3\t1\t1\tUNSAT\t0\t\n"
                + "0000000000000003\t2\tAABB\t11\tpending\t0\t0\t\t0\t\n"
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
                HEADER + "0000000000000001\t0\tBBBB\t8\tpending\t0\t1\tUNKNOWN\t0\t\n"
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
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t0\t\t0\t\n"
                + "0000000000000002\t1\tABBB\t9\tcertified-in-S3\t1\t0\t\t0\t\n"
            )
            self.assertEqual(select_unknowns(coverage, read_jobs(jobs)), [])
            coverage.write_text(
                HEADER
                + "0000000000000001\t0\tBBBB\t7\tpending\t0\t0\t\t0\t\n"
                + "0000000000000002\t1\tABBB\t9\tpending\t0\t1\tUNKNOWN\t0\t\n"
            )
            with self.assertRaisesRegex(ValueError, "retry tag absent from jobs"):
                select_unknowns(coverage, read_jobs(jobs))

    def test_v3_claim_or_verdict_blocks_same_cap_retry(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jobs = root / "jobs.tsv"
            jobs.write_text("0000000000000001\t0\tBBBB\t7\n")
            coverage = root / "coverage.tsv"
            for v3_claim, v3_verdict in (("1", ""), ("1", "UNKNOWN")):
                coverage.write_text(
                    HEADER
                    + "0000000000000001\t0\tBBBB\t7\tpending\t0\t1\tUNKNOWN\t"
                    + v3_claim + "\t" + v3_verdict + "\n"
                )
                self.assertEqual(select_unknowns(coverage, read_jobs(jobs)), [])

    def test_present_canonical_key_is_not_an_ordinary_corrupt_key_repair(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            jobs = root / "jobs.tsv"
            jobs.write_text("0000000000000001\t0\tBBBB\t7\n")
            coverage = root / "coverage.tsv"
            coverage.write_text(
                HEADER
                + "0000000000000001\t0\tBBBB\t7\tcertified-in-S3\t1\t1\t"
                + "UNKNOWN\t0\t\n"
            )
            self.assertEqual(select_unknowns(coverage, read_jobs(jobs)), [])

    def test_pinned_orphan_claim_is_requeued_only_in_exact_pending_state(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tag = "0000000000000001"
            jobs_path = root / "jobs.tsv"
            jobs_path.write_text(f"{tag}\t0\tBBBB\t7\n")
            jobs = read_jobs(jobs_path)
            evidence_path = root / "orphans.txt"
            evidence = f"{V2_CLAIM_PREFIX}{tag}\n".encode()
            self.assertEqual(read_orphan_tags_bytes(evidence_path, evidence), {tag})
            coverage = (
                HEADER + f"{tag}\t0\tBBBB\t7\tpending\t0\t0\t\t0\t\n"
            ).encode()
            self.assertEqual(
                select_unknowns_bytes(Path("coverage.tsv"), coverage, jobs, {tag}),
                [f"{tag}\t0\tBBBB\t7"],
            )
            changed = coverage.replace(b"\tpending\t0\t0\t", b"\tcertified-in-S3\t1\t0\t")
            with self.assertRaisesRegex(ValueError, "acquired terminal or claim evidence"):
                select_unknowns_bytes(Path("coverage.tsv"), changed, jobs, {tag})

    def test_orphan_evidence_format_and_universe_fail_closed(self) -> None:
        path = Path("orphans.txt")
        with self.assertRaisesRegex(ValueError, "unique, and sorted"):
            read_orphan_tags_bytes(
                path,
                (f"{V2_CLAIM_PREFIX}0000000000000002\n"
                 f"{V2_CLAIM_PREFIX}0000000000000001\n").encode(),
            )
        with self.assertRaisesRegex(ValueError, "wrong orphan claim prefix"):
            read_orphan_tags_bytes(path, b"wrong/0000000000000001\n")
        jobs = {"0000000000000001": (0, "BBBB", 7, "0000000000000001\t0\tBBBB\t7")}
        coverage = (
            HEADER + "0000000000000001\t0\tBBBB\t7\tpending\t0\t0\t\t0\t\n"
        ).encode()
        with self.assertRaisesRegex(ValueError, "absent from coverage"):
            select_unknowns_bytes(Path("coverage.tsv"), coverage, jobs,
                                  {"0000000000000002"})


if __name__ == "__main__":
    unittest.main()
