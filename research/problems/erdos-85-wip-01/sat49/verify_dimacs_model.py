#!/usr/bin/env python3
"""Independently verify a complete SAT-competition model against DIMACS CNF."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path
from typing import cast


class VerificationError(ValueError):
    pass


def read_model(path: Path) -> tuple[list[bool], str]:
    digest = hashlib.sha256()
    status_count = 0
    literals: list[int] = []
    model_terminated = False
    with path.open("rb") as source:
        for line_number, raw in enumerate(source, 1):
            digest.update(raw)
            try:
                line = raw.decode("ascii").strip()
            except UnicodeDecodeError as error:
                raise VerificationError(f"{path}:{line_number}: non-ASCII model") from error
            if not line or line.startswith("c"):
                continue
            fields = line.split()
            if fields[:1] == ["s"]:
                if fields != ["s", "SATISFIABLE"]:
                    raise VerificationError(f"{path}:{line_number}: status is not SATISFIABLE")
                status_count += 1
            elif fields[:1] == ["v"]:
                if model_terminated:
                    raise VerificationError(f"{path}:{line_number}: assignment after model terminator")
                try:
                    values = [int(field) for field in fields[1:]]
                except ValueError as error:
                    raise VerificationError(f"{path}:{line_number}: malformed model literal") from error
                if not values or 0 in values[:-1]:
                    raise VerificationError(f"{path}:{line_number}: malformed model assignment")
                if values[-1] == 0:
                    model_terminated = True
                    values.pop()
                literals.extend(values)
            else:
                raise VerificationError(f"{path}:{line_number}: unexpected model line")
    if status_count != 1:
        raise VerificationError(f"{path}: expected exactly one SATISFIABLE status")
    if not model_terminated:
        raise VerificationError(f"{path}: unterminated model assignment")
    maximum = max((abs(literal) for literal in literals), default=0)
    assignment: list[bool | None] = [None] * (maximum + 1)
    for literal in literals:
        variable = abs(literal)
        value = literal > 0
        if assignment[variable] is not None:
            raise VerificationError(f"{path}: duplicate assignment for variable {variable}")
        assignment[variable] = value
    return cast(list[bool], assignment), digest.hexdigest()


def verify(cnf_path: Path, model_path: Path) -> tuple[int, int, str, str]:
    assignment, model_sha = read_model(model_path)
    cnf_digest = hashlib.sha256()
    header: tuple[int, int] | None = None
    clause: list[int] = []
    clauses = 0

    with cnf_path.open("rb") as source:
        for line_number, raw in enumerate(source, 1):
            cnf_digest.update(raw)
            try:
                line = raw.decode("ascii").strip()
            except UnicodeDecodeError as error:
                raise VerificationError(f"{cnf_path}:{line_number}: non-ASCII CNF") from error
            if not line or line.startswith("c"):
                continue
            fields = line.split()
            if fields[:1] == ["p"]:
                if header is not None or clause or len(fields) != 4 or fields[1] != "cnf":
                    raise VerificationError(f"{cnf_path}:{line_number}: malformed or duplicate header")
                try:
                    variables, expected_clauses = int(fields[2]), int(fields[3])
                except ValueError as error:
                    raise VerificationError(f"{cnf_path}:{line_number}: malformed header counts") from error
                if variables < 0 or expected_clauses < 0:
                    raise VerificationError(f"{cnf_path}:{line_number}: negative header count")
                header = variables, expected_clauses
                if len(assignment) != variables + 1 or any(value is None for value in assignment[1:]):
                    raise VerificationError(
                        f"{model_path}: assignment is not complete for variables 1..{variables}"
                    )
                continue
            if header is None:
                raise VerificationError(f"{cnf_path}:{line_number}: clause before header")
            try:
                tokens = [int(field) for field in fields]
            except ValueError as error:
                raise VerificationError(f"{cnf_path}:{line_number}: malformed clause literal") from error
            for literal in tokens:
                if literal:
                    if abs(literal) > header[0]:
                        raise VerificationError(
                            f"{cnf_path}:{line_number}: variable {abs(literal)} exceeds header"
                        )
                    clause.append(literal)
                    continue
                clauses += 1
                if not any(bool(assignment[abs(item)]) == (item > 0) for item in clause):
                    raise VerificationError(f"{cnf_path}: clause {clauses} is not satisfied")
                clause.clear()

    if header is None:
        raise VerificationError(f"{cnf_path}: missing header")
    if clause:
        raise VerificationError(f"{cnf_path}: unterminated final clause")
    if clauses != header[1]:
        raise VerificationError(
            f"{cnf_path}: header declares {header[1]} clauses but parsed {clauses}"
        )
    return header[0], clauses, cnf_digest.hexdigest(), model_sha


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    try:
        variables, clauses, cnf_sha, model_sha = verify(args.cnf, args.model)
    except (OSError, VerificationError) as error:
        print(f"MODEL INVALID: {error}", file=sys.stderr)
        return 1
    print(
        f"MODEL VERIFIED variables={variables} clauses={clauses} "
        f"cnf_sha256={cnf_sha} model_sha256={model_sha}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
