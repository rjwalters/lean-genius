#!/usr/bin/env python3
"""Strict input checks for bounded verdict-only CNF materialization.

The Lean v2 emitter's clause comparator ignores headers and empty clauses.
Pair its MATCH(count,top) with this validator; MATCH alone is insufficient.
"""
from pathlib import Path
import hashlib
import re

MAX_INPUT_BYTES = 99_000_000
MAX_LINE_BYTES = 1_000_000
INTEGER = re.compile(rb"(?:0|-?[1-9][0-9]*)")
MATCH = re.compile(r"MATCH \(([0-9]+) clauses, top ([0-9]+)\)")


def validate_dimacs(path: Path, *, expected_variables: int | None = None,
                    expected_clauses: int | None = None) -> dict:
    """Count every clause terminator, including empty clauses; check all literals."""
    header = None
    count = 0
    pending = False
    size = 0
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while line := source.readline(MAX_LINE_BYTES + 1):
            size += len(line)
            if size > MAX_INPUT_BYTES or len(line) > MAX_LINE_BYTES:
                raise ValueError("CNF exceeds bounded input/line size")
            digest.update(line)
            stripped = line.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            tokens = stripped.split()
            if tokens[0] == b"p":
                if header is not None or len(tokens) != 4 or tokens[1] != b"cnf":
                    raise ValueError("Missing, duplicate or invalid DIMACS header")
                if not all(re.fullmatch(rb"[0-9]+", x) for x in tokens[2:]):
                    raise ValueError("Invalid DIMACS header counts")
                header = tuple(map(int, tokens[2:]))
                continue
            if header is None:
                raise ValueError("Clause data precedes DIMACS header")
            for token in tokens:
                if not INTEGER.fullmatch(token):
                    raise ValueError("Invalid DIMACS literal")
                literal = int(token)
                if abs(literal) > header[0]:
                    raise ValueError("Literal exceeds DIMACS variable bound")
                if literal == 0:
                    count += 1
                    pending = False
                else:
                    pending = True
    if header is None or pending:
        raise ValueError("Missing header or unterminated final clause")
    if count != header[1]:
        raise ValueError("Actual clause count differs from DIMACS header")
    if expected_variables is not None and header[0] != expected_variables:
        raise ValueError("DIMACS variables differ from generator MATCH")
    if expected_clauses is not None and count != expected_clauses:
        raise ValueError("DIMACS clauses differ from generator MATCH")
    return {"variables": header[0], "clauses": count, "bytes": size,
            "sha256": digest.hexdigest()}


def validate_emitter_match(path: Path, returncode: int, stdout: str) -> dict:
    """Require exactly one successful generator MATCH and matching strict DIMACS."""
    match = MATCH.fullmatch(stdout.strip())
    if returncode != 0 or match is None:
        raise ValueError("Generator check did not return a unique successful MATCH")
    clauses, variables = map(int, match.groups())
    return validate_dimacs(path, expected_variables=variables, expected_clauses=clauses)
