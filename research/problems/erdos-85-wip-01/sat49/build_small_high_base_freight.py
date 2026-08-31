#!/usr/bin/env python3
"""Create and receipt the seven Lean-emitted small-high base CNFs.

This is a prelaunch freight builder, not a solver launcher.  It refuses a
dirty repository or untracked emitter source, atomically reserves a previously
absent destination, and publishes the receipt last as its commit marker.  A
regenerated root queue is not launchable unless its own reviewed receipt hashes
this freight receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PROOFS = REPO / "proofs"
EMITTER = PROOFS / "Proofs/Erdos85OrderFortyNineSmallHighCnfEmit.lean"
CELLS = ("h3_b1", "h3_c1", "h3_c2", "h3_dist2",
         "h5_t0", "h5_t1", "h5_t2")
SCHEMA = "erdos85-small-high-base-freight-v1"
BUILDER = Path(__file__).resolve()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=repo, text=True, capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def require_clean_tracked_source(repo: Path, source: Path) -> tuple[str, str]:
    relative = source.resolve().relative_to(repo.resolve()).as_posix()
    tracked = git(repo, "ls-files", "--error-unmatch", "--", relative)
    if tracked != relative:
        raise ValueError("emitter source is not tracked at HEAD")
    if git(repo, "status", "--porcelain=v1", "--", relative):
        raise ValueError("emitter source is dirty")
    head_bytes = subprocess.run(
        ["git", "show", f"HEAD:{relative}"], cwd=repo,
        capture_output=True, check=False)
    if head_bytes.returncode != 0 or head_bytes.stdout != source.read_bytes():
        raise ValueError("emitter bytes differ from HEAD")
    return git(repo, "rev-parse", "HEAD"), relative


def require_clean_repo(repo: Path, expected_commit: str | None = None) -> str:
    commit = git(repo, "rev-parse", "HEAD")
    if expected_commit is not None and commit != expected_commit:
        raise ValueError("repository HEAD changed during freight construction")
    if git(repo, "status", "--porcelain=v1", "--untracked-files=all"):
        raise ValueError("repository is dirty")
    return commit


def build_emitter(proofs: Path) -> list[str]:
    command = ["lake", "build", "Proofs.Erdos85OrderFortyNineSmallHighCnfEmit"]
    result = subprocess.run(
        command, cwd=proofs, text=True, capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError("Lean emitter build failed:\n" + result.stderr)
    return command


def emit_cell(proofs: Path, source: Path, cell: str, output: Path) -> list[str]:
    command = ["lake", "env", "lean", "--run", str(source), cell]
    with output.open("xb") as stream:
        result = subprocess.run(
            command, cwd=proofs, stdout=stream, stderr=subprocess.PIPE,
            check=False)
    if result.returncode != 0:
        raise ValueError(
            f"Lean emitter failed for {cell} with rc={result.returncode}: "
            + result.stderr.decode(errors="replace"))
    return command


def validate_dimacs(path: Path) -> dict[str, int]:
    with path.open("rb") as stream:
        header = stream.readline()
        try:
            fields = header.decode("ascii").rstrip("\n").split()
        except UnicodeDecodeError as error:
            raise ValueError(f"{path.name}: non-ASCII header") from error
        if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
            raise ValueError(f"{path.name}: malformed DIMACS header")
        try:
            variables, expected_clauses = map(int, fields[2:])
        except ValueError as error:
            raise ValueError(f"{path.name}: non-integer DIMACS header") from error
        if variables <= 0 or expected_clauses <= 0:
            raise ValueError(f"{path.name}: non-positive DIMACS dimensions")
        clauses = 0
        maximum = 0
        for line_number, raw in enumerate(stream, 2):
            if not raw.endswith(b"\n"):
                raise ValueError(f"{path.name}:{line_number}: missing final newline")
            try:
                values = [int(value) for value in raw.split()]
            except ValueError as error:
                raise ValueError(f"{path.name}:{line_number}: non-integer literal") from error
            if len(values) < 2 or values[-1] != 0 or 0 in values[:-1]:
                raise ValueError(f"{path.name}:{line_number}: malformed clause terminator")
            maximum = max(maximum, *(abs(value) for value in values[:-1]))
            clauses += 1
        if clauses != expected_clauses:
            raise ValueError(
                f"{path.name}: header says {expected_clauses} clauses, found {clauses}")
        if maximum > variables:
            raise ValueError(
                f"{path.name}: maximum literal {maximum} exceeds top {variables}")
    return {"variables": variables, "clauses": clauses, "max_literal": maximum}


def publish_freight(temporary: Path, output: Path) -> None:
    """Commit a staged freight directory, with receipt.json as commit marker."""
    if os.path.lexists(output):
        raise ValueError("output freight directory already exists")
    reserved = False
    try:
        os.mkdir(output)
        reserved = True
        for cell in CELLS:
            os.rename(temporary / f"{cell}.cnf", output / f"{cell}.cnf")
        os.rename(temporary / "receipt.json", output / "receipt.json")
        temporary.rmdir()
    except FileExistsError as error:
        raise ValueError("output freight directory already exists") from error
    except BaseException:
        if reserved and not (output / "receipt.json").exists():
            shutil.rmtree(output, ignore_errors=True)
        raise


def build(output: Path, repo: Path = REPO, proofs: Path = PROOFS,
          source: Path = EMITTER, builder: Path = BUILDER) -> dict[str, object]:
    if os.path.lexists(output):
        raise ValueError("output freight directory already exists")
    commit = require_clean_repo(repo)
    commit, relative_source = require_clean_tracked_source(repo, source)
    builder_commit, relative_builder = require_clean_tracked_source(repo, builder)
    if builder_commit != commit:
        raise ValueError("emitter and freight builder are not at one commit")
    build_command = build_emitter(proofs)
    require_clean_repo(repo, commit)
    require_clean_tracked_source(repo, source)
    require_clean_tracked_source(repo, builder)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}.", dir=output.parent))
    try:
        rows: list[dict[str, object]] = []
        expected_command: list[str] | None = None
        for cell in CELLS:
            destination = temporary / f"{cell}.cnf"
            command = emit_cell(proofs, source, cell, destination)
            command_shape = [*command[:-1], "<cell>"]
            if expected_command is None:
                expected_command = command_shape
            elif command_shape != expected_command:
                raise ValueError("emitter command shape changed between cells")
            dimensions = validate_dimacs(destination)
            rows.append({
                "cell": cell,
                "path": destination.name,
                "sha256": sha256_file(destination),
                "bytes": destination.stat().st_size,
                **dimensions,
            })
        lean_version = subprocess.run(
            ["lake", "env", "lean", "--version"], cwd=proofs,
            text=True, capture_output=True, check=False)
        if lean_version.returncode != 0:
            raise ValueError("cannot record Lean version: " + lean_version.stderr.strip())
        receipt: dict[str, object] = {
            "schema": SCHEMA,
            "git_commit": commit,
            "freight_builder_source": relative_builder,
            "freight_builder_sha256": sha256_file(builder),
            "emitter_source": relative_source,
            "emitter_sha256": sha256_file(source),
            "emitter_build_command": build_command,
            "emitter_command": expected_command,
            "lean_version": lean_version.stdout.strip(),
            "cells": rows,
        }
        (temporary / "receipt.json").write_bytes(canonical_json(receipt))
        require_clean_repo(repo, commit)
        require_clean_tracked_source(repo, source)
        require_clean_tracked_source(repo, builder)
        publish_freight(temporary, output)
        return receipt
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = build(args.output.resolve())
    print(canonical_json(receipt).decode(), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
