#!/usr/bin/env python3
"""Solve profile-3/4 reciprocal rows against Lean-exact v2 CNFs.

This is intentionally separate from the live profile-2 campaign runner.  It
accepts one uniform AAAB/profile-3 or AAAA/profile-4 seed queue, emits and
checks Lean's authoritative CNF, disables Kissat's fresh-variable BVA passes,
and requires drat-trim verification before writing a resumable verdict.
"""

from __future__ import annotations

import argparse
import subprocess
import time
from pathlib import Path


BASE = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49")
IMAGE = "lean4-arm64:v4.31.0"
DRAT_TRIM = BASE / "v2-tier1-work/bin/drat-trim"
FAMILY = {"3": "AAAB", "4": "AAAA"}


def to_data(path: Path) -> str:
    resolved = path.resolve()
    try:
        relative = resolved.relative_to(BASE)
    except ValueError as error:
        raise ValueError(f"path is outside the mounted artifact root: {path}") from error
    return "/data/" + str(relative)


def docker_v2cnf(arguments: list[str], **kwargs: object) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            "docker",
            "run",
            "--rm",
            "--memory=12g",
            "--cpus=2",
            "-v",
            "lean-mathlib-cache:/cache",
            "-v",
            f"{BASE}:/data",
            IMAGE,
            "/cache/bin/v2cnf",
            *arguments,
        ],
        **kwargs,
    )


def verified(verdict: Path, tag: str, profile: str) -> bool:
    if not verdict.is_file():
        return False
    fields = verdict.read_text().split()
    return (
        len(fields) >= 8
        and fields[0] == tag
        and fields[1] == "UNSAT"
        and fields[3] == "drat:VERIFIED"
        and fields[4] == "mode:MONO"
        and fields[5] == "arm:v2"
        and fields[6] == "lean-exact:MATCH"
        and fields[7] == f"profile:{profile}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("jobs", type=Path, help="seven-field seed jobs TSV")
    parser.add_argument("outdir", type=Path)
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be positive")
    if not DRAT_TRIM.is_file():
        raise FileNotFoundError(DRAT_TRIM)

    jobs: list[tuple[str, str, Path]] = []
    queue_profile: str | None = None
    for line_number, raw in enumerate(args.jobs.read_text().splitlines(), 1):
        fields = raw.split("\t")
        if len(fields) != 7:
            raise ValueError(f"{args.jobs}:{line_number}: expected seven fields")
        tag, profile, family, mode, table, _cnf, _drat = fields
        if profile not in FAMILY or family != FAMILY[profile] or mode != "MONO":
            raise ValueError(f"{args.jobs}:{line_number}: invalid profile/family/mode")
        if queue_profile is None:
            queue_profile = profile
        elif profile != queue_profile:
            raise ValueError("jobs file mixes profiles; use one output directory per profile")
        jobs.append((tag, profile, Path(table)))
    if not jobs:
        raise ValueError("jobs file is empty")
    if args.limit is not None:
        jobs = jobs[: args.limit]

    args.outdir.mkdir(parents=True, exist_ok=True)
    pending = [
        job for job in jobs
        if not verified(args.outdir / f"{job[0]}.v2.verdict", job[0], job[1])
    ]
    print(f"profile={queue_profile} jobs={len(jobs)} pending={len(pending)}", flush=True)

    for index, (tag, profile, table) in enumerate(pending, 1):
        cnf = args.outdir / f"{tag}.v2.cnf"
        drat = args.outdir / f"{tag}.v2.drat"
        drat_gz = args.outdir / f"{tag}.v2.drat.gz"
        core = args.outdir / f"{tag}.v2.core.cnf"
        kissat_log = args.outdir / f"{tag}.kissat.log"
        trim_log = args.outdir / f"{tag}.drat-trim.log"
        verdict = args.outdir / f"{tag}.v2.verdict"
        for partial in (cnf, drat, drat_gz, core, kissat_log, trim_log):
            partial.unlink(missing_ok=True)

        with cnf.open("wb") as stream:
            emitted = docker_v2cnf(
                ["emit", profile, to_data(table)],
                stdout=stream,
                stderr=subprocess.PIPE,
                timeout=900,
            )
        if emitted.returncode != 0 or cnf.stat().st_size == 0:
            raise RuntimeError(f"{tag}: v2cnf emit failed: {emitted.stderr!r}")
        checked = docker_v2cnf(
            ["check", profile, to_data(table), to_data(cnf)],
            capture_output=True,
            text=True,
            timeout=900,
        )
        if checked.returncode != 0 or "MATCH" not in checked.stdout:
            raise RuntimeError(f"{tag}: exact CNF check failed: {checked.stdout} {checked.stderr}")

        started = time.monotonic()
        with kissat_log.open("w") as stream:
            solved = subprocess.run(
                [
                    "kissat",
                    "-f",
                    "--no-binary",
                    "--no-factor",
                    "--no-preprocessfactor",
                    str(cnf),
                    str(drat),
                ],
                stdout=stream,
                stderr=subprocess.STDOUT,
                timeout=3600,
            )
        elapsed = time.monotonic() - started
        if solved.returncode != 20 or not drat.is_file():
            raise RuntimeError(f"{tag}: Kissat did not return UNSAT (rc={solved.returncode})")

        trimmed = subprocess.run(
            [str(DRAT_TRIM), str(cnf), str(drat), "-c", str(core)],
            capture_output=True,
            text=True,
            timeout=3600,
        )
        trim_log.write_text(trimmed.stdout + trimmed.stderr)
        if trimmed.returncode != 0 or "s VERIFIED" not in trimmed.stdout:
            raise RuntimeError(f"{tag}: drat-trim did not verify")
        subprocess.run(["gzip", "-f", str(drat)], check=True, timeout=1800)
        verdict.write_text(
            f"{tag} UNSAT {elapsed:.1f}s drat:VERIFIED mode:MONO arm:v2 "
            f"lean-exact:MATCH profile:{profile}\n"
        )
        print(f"[{index}/{len(pending)}] {verdict.read_text().strip()}", flush=True)

    print("LEAN-EXACT QUEUE DONE", flush=True)


if __name__ == "__main__":
    main()
