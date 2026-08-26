#!/usr/bin/env python3
"""Run one H7 CNF with CaDiCaL's native LRAT output and emit a receipt."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import os
import re
import subprocess
import tempfile
from pathlib import Path


JOB_RE = re.compile(
    r"cube_F[6-9]_t\d+(?:\.split-[01]|\.adaptive\.leaf-[01]+)?")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_receipt(job_id: str, cnf: Path, proof_gz: Path) -> str:
    if JOB_RE.fullmatch(job_id) is None:
        raise ValueError(f"invalid H7 job id: {job_id}")
    return (f"{job_id} {sha256(cnf)} {sha256(proof_gz)} "
            f"{proof_gz.stat().st_size}")


def run(job_id: str, cnf: Path, output_dir: Path, cadical: Path,
        lrat_check: Path, time_limit: int) -> tuple[Path, str]:
    if JOB_RE.fullmatch(job_id) is None:
        raise ValueError(f"invalid H7 job id: {job_id}")
    if time_limit <= 0:
        raise ValueError("time limit must be positive")
    for path, label in ((cnf, "CNF"), (cadical, "CaDiCaL"),
                        (lrat_check, "lrat-check")):
        if not path.is_file():
            raise ValueError(f"missing {label}: {path}")
    output_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{job_id}.", dir=output_dir) as raw:
        work = Path(raw)
        proof = work / f"{job_id}.lrat"
        solve_log = work / "cadical.log"
        with solve_log.open("wb") as log:
            solved = subprocess.run(
                [str(cadical), "--lrat", "--no-binary", "--checkproof=3",
                 "-t", str(time_limit), str(cnf), str(proof)],
                stdout=log, stderr=subprocess.STDOUT, timeout=time_limit + 60)
        if solved.returncode != 20 or not proof.is_file():
            raise RuntimeError(
                f"{job_id}: CaDiCaL did not produce checked UNSAT (exit "
                f"{solved.returncode})")
        checked = subprocess.run(
            [str(lrat_check), str(cnf), str(proof)], capture_output=True,
            text=True, timeout=max(300, time_limit))
        verdicts = {line.strip() for line in checked.stdout.splitlines()}
        if checked.returncode or "c VERIFIED" not in verdicts:
            raise RuntimeError(f"{job_id}: independent lrat-check rejected proof")
        destination = output_dir / f"{job_id}.lrat.gz"
        temporary = output_dir / f".{job_id}.lrat.gz.tmp"
        try:
            with proof.open("rb") as source, temporary.open("wb") as raw_target:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw_target,
                                   mtime=0) as target:
                    for chunk in iter(lambda: source.read(1 << 20), b""):
                        target.write(chunk)
            os.replace(temporary, destination)
        finally:
            temporary.unlink(missing_ok=True)
    return destination, canonical_receipt(job_id, cnf, destination)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--cadical", type=Path, default=Path("/opt/homebrew/bin/cadical"))
    parser.add_argument("--lrat-check", type=Path, required=True)
    parser.add_argument("--time-limit", type=int, default=3600)
    args = parser.parse_args()
    proof, receipt = run(args.job_id, args.cnf.resolve(), args.output_dir.resolve(),
                         args.cadical.resolve(), args.lrat_check.resolve(),
                         args.time_limit)
    print(receipt)
    print(f"WROTE {proof}")


if __name__ == "__main__":
    main()
