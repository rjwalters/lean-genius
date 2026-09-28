"""Deterministic git-history evidence mining for inventorship (issue #445).

Evidence substrate for the ``ip-uspto-inventorship --evidence`` mode: given
a repository path and an element->paths map (``inventorship_map.json``),
mine the repo's git history into evidence rows (``evidence.jsonl``) that
the command's LLM step classifies and renders into the inventorship
matrix's **Notes column only**.

Legal framing (load-bearing — do not weaken)
--------------------------------------------

Git history documents **reduction to practice** (who committed working
implementation), NOT **conception** (the legal test for inventorship).
This module therefore only *collects*; it never attributes inventorship.
Every consumer must label git-derived annotations as reduction-to-practice
evidence and keep the existing "never guess attribution" rules governing
the matrix's ``●`` cells. Evidence is advisory: it informs the attorney
interview, never adjudicates, and never adds or removes named inventors.

Design contract (settled at #445 curation; do NOT re-litigate)
--------------------------------------------------------------

- **Pure stdlib + subprocess git.** No new Python deps; degrade
  gracefully when ``git`` is unavailable or the path is not a repo
  (precedent: the ``check_*_available()`` family in ``anvil/lib/render.py``).
- **Collection only.** Classification (``conception`` / ``implementation``
  / ``mixed`` / ``unclassified``) is the LLM step in the command prose —
  and must classify on diff content, never commit message alone. Rows
  leave here as ``classification="unclassified"``.
- **Consumer-agnostic inputs**: ``(repo_path, element->paths map)``. No
  BRIEF/claims parsing in this module. Promoted to ``anvil/lib/`` (issue
  #516) once ``anvil:ip-uspto-provisional``'s inventorship-lite pass became
  the second consumer (lib-promotion convention). Both consumers invoke
  this module by direct file path at
  ``anvil/lib/inventorship_evidence.py`` (``.anvil/anvil/lib/...`` in an
  installed consumer repo): ``anvil:ip-uspto``'s ``--evidence`` mode and
  the provisional's ``ip-uspto-provisional-inventorship`` lite pass. The
  ip-uspto skill's ``inventorship_interview.py`` also loads
  ``is_vendored_path`` from this canonical location via ``importlib``.
- **Native schemas adopted as-is** (so a future sphere migration
  round-trips): ``inventorship_map.json`` path roles
  (``primary`` / ``vendored-primary`` / ``diverged-copy`` / ``supporting``,
  ``manually_seeded``, ``seeded_at``) and the ``evidence.jsonl`` row
  ``{path, sha, author, email, date, subject, claim_element,
  classification, rationale}``.
- **Vendored detection**: a mapped path is BLOCKED (upstream history
  required, never silent) when its role is ``vendored-primary`` or it
  matches a ``vendored_prefixes`` entry in the map. Separately, the
  native heuristic flags ``suspected-vendored`` when a path's add-commit
  touches more than :data:`VENDOR_FILE_THRESHOLD` files AND its message
  matches :data:`VENDOR_MESSAGE_RE` — prompt the operator.
- **CLI contract** per the tool-evidence precedents
  (``anvil/lib/hyperlink_resolver.py``, memo's ``citation_coverage.py``):
  JSON to stdout; exit ``0`` = clean collection, ``1`` = findings
  (vendored/BLOCKED paths, stale map paths, no-history paths,
  suspected-vendored), ``2`` = invocation error (bad map, no git, not a
  repo). Consumers invoke this file by direct path
  (``python3 anvil/lib/inventorship_evidence.py``) — the calling skill
  dirs are hyphenated, so command prose references the file path rather
  than a dotted ``python -m`` path (project-migrate/project-share
  precedent). The module is also importable as
  ``anvil.lib.inventorship_evidence`` (the canonical import path tested in
  ``tests/lib/test_inventorship_evidence_promotion.py``).
"""

from __future__ import annotations

import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

# The git executable. Module-level so tests can point it at a nonexistent
# binary to exercise the graceful-degradation path.
GIT = "git"

#: Per-commit diff budget (chars) for the LLM classification step.
DEFAULT_DIFF_BUDGET = 4000

#: Native vendored-code heuristic: an add-commit touching more than this
#: many files AND matching :data:`VENDOR_MESSAGE_RE` is suspected-vendored.
VENDOR_FILE_THRESHOLD = 50

#: Native vendored-commit message heuristic (adopted verbatim).
VENDOR_MESSAGE_RE = re.compile(r"(?i)\b(vendor|import|port|migrat|consolidat)\b")

#: Valid path roles in ``inventorship_map.json`` (native schema).
ROLES = ("primary", "vendored-primary", "diverged-copy", "supporting")

#: Valid classification values for ``evidence.jsonl`` rows. This module
#: always emits ``"unclassified"`` — classification is the LLM step.
CLASSIFICATIONS = ("conception", "implementation", "mixed", "unclassified")

#: Finding types surfaced in the result (all of them imply exit code 1).
FINDING_VENDORED = "vendored-path"          # BLOCKED: upstream history required
FINDING_SUSPECTED_VENDORED = "suspected-vendored"  # prompt operator
FINDING_STALE_PATH = "stale-path"           # mapped path gone; prompt, never silently update
FINDING_NO_HISTORY = "no-history"           # path exists but has zero commits

_FIELD_SEP = "\x1f"
_LOG_FORMAT = "%H%x1f%an%x1f%ae%x1f%aI%x1f%s"

#: The unique-identity key of an evidence row (append-only dedupe key).
_ROW_KEY_FIELDS = ("path", "sha", "claim_element")

EVIDENCE_ROW_FIELDS = (
    "path",
    "sha",
    "author",
    "email",
    "date",
    "subject",
    "claim_element",
    "classification",
    "rationale",
)


class EvidenceError(Exception):
    """Invocation-level error (maps to CLI exit code 2)."""


# ---------------------------------------------------------------------------
# git plumbing
# ---------------------------------------------------------------------------


def _run_git(repo: Path, args: List[str]) -> subprocess.CompletedProcess:
    """Run ``git -C <repo> <args>``; never raises on nonzero exit."""
    return subprocess.run(
        [GIT, "-C", str(repo), *args],
        capture_output=True,
        text=True,
    )


def check_git_available() -> bool:
    """True when the ``git`` binary is invocable (graceful-degradation gate)."""
    try:
        proc = subprocess.run([GIT, "--version"], capture_output=True, text=True)
    except (FileNotFoundError, OSError):
        return False
    return proc.returncode == 0


def git_toplevel(path: Path) -> Optional[Path]:
    """The repo toplevel containing ``path``, or None when not a git repo."""
    try:
        proc = _run_git(path, ["rev-parse", "--show-toplevel"])
    except (FileNotFoundError, OSError):
        return None
    if proc.returncode != 0:
        return None
    top = proc.stdout.strip()
    return Path(top) if top else None


def path_history(repo: Path, path: str) -> List[Dict[str, str]]:
    """Commit history for ``path`` (newest first), following renames.

    Each entry: ``{sha, author, email, date, subject}``. An empty repo,
    an unknown path, or a path with zero commits all yield ``[]``.
    """
    proc = _run_git(
        repo,
        ["log", "--follow", f"--format={_LOG_FORMAT}", "--", path],
    )
    if proc.returncode != 0:
        return []
    return _parse_log_records(proc.stdout)


def add_commit(repo: Path, path: str) -> Optional[Dict[str, str]]:
    """The commit that ADDED ``path`` (``--diff-filter=A``, rename-aware).

    Returns the oldest matching record, or None when the path has no
    add-commit in history.
    """
    proc = _run_git(
        repo,
        [
            "log",
            "--follow",
            "--diff-filter=A",
            f"--format={_LOG_FORMAT}",
            "--",
            path,
        ],
    )
    if proc.returncode != 0:
        return None
    records = _parse_log_records(proc.stdout)
    return records[-1] if records else None


def _parse_log_records(stdout: str) -> List[Dict[str, str]]:
    records: List[Dict[str, str]] = []
    for line in stdout.splitlines():
        parts = line.split(_FIELD_SEP)
        if len(parts) != 5:
            continue
        sha, author, email, date, subject = parts
        records.append(
            {
                "sha": sha,
                "author": author,
                "email": email,
                "date": date,
                "subject": subject,
            }
        )
    return records


def commit_file_count(repo: Path, sha: str) -> int:
    """Number of paths touched by ``sha`` (``--root``-safe for the first commit)."""
    proc = _run_git(
        repo,
        ["diff-tree", "--no-commit-id", "--name-only", "-r", "--root", sha],
    )
    if proc.returncode != 0:
        return 0
    return sum(1 for line in proc.stdout.splitlines() if line.strip())


def commit_diff(
    repo: Path,
    sha: str,
    path: Optional[str] = None,
    budget: int = DEFAULT_DIFF_BUDGET,
) -> str:
    """``git show --stat --patch`` for ``sha`` (optionally one path), truncated.

    The classification step reads this — diff content, never commit
    message alone — so the budget keeps per-commit context bounded
    (~4000 chars by default, the native default).
    """
    args = ["show", "--stat", "--patch", "--format=%H %an %aI%n%s", sha]
    if path is not None:
        args += ["--", path]
    proc = _run_git(repo, args)
    if proc.returncode != 0:
        return ""
    text = proc.stdout
    if len(text) > budget:
        return text[:budget] + f"\n... [truncated at {budget} chars]"
    return text


_BLAME_HEADER_RE = re.compile(r"^([0-9a-f]{40})\s+\d+\s+(\d+)(?:\s+\d+)?$")


def blame_line_range(
    repo: Path, path: str, start: int, end: int
) -> List[Dict[str, Any]]:
    """``git blame --line-porcelain -L start,end`` parsed per line.

    Each entry: ``{sha, author, line, content}``. Empty list on any git
    failure (missing path, empty repo, bad range).
    """
    proc = _run_git(
        repo,
        ["blame", "--line-porcelain", "-L", f"{start},{end}", "--", path],
    )
    if proc.returncode != 0:
        return []
    entries: List[Dict[str, Any]] = []
    authors_by_sha: Dict[str, str] = {}
    sha: Optional[str] = None
    line_no: Optional[int] = None
    for raw in proc.stdout.splitlines():
        header = _BLAME_HEADER_RE.match(raw)
        if header:
            sha = header.group(1)
            line_no = int(header.group(2))
            continue
        # ``author`` lines only appear on a commit's FIRST occurrence in
        # porcelain output, so cache per sha rather than per group.
        if raw.startswith("author ") and sha is not None:
            authors_by_sha[sha] = raw[len("author "):]
            continue
        if raw.startswith("\t") and sha is not None and line_no is not None:
            entries.append(
                {
                    "sha": sha,
                    "author": authors_by_sha.get(sha, ""),
                    "line": line_no,
                    "content": raw[1:],
                }
            )
            sha = None
            line_no = None
    return entries


# ---------------------------------------------------------------------------
# map loading / validation
# ---------------------------------------------------------------------------


def load_map(map_path: Path) -> Dict[str, Any]:
    """Load + validate ``inventorship_map.json``. Raises EvidenceError."""
    if not map_path.is_file():
        raise EvidenceError(f"map file does not exist: {map_path}")
    try:
        data = json.loads(map_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise EvidenceError(f"map file is not valid JSON: {map_path}: {exc}")
    errors = validate_map(data)
    if errors:
        raise EvidenceError(
            "invalid inventorship_map.json: " + "; ".join(errors)
        )
    return data


def validate_map(data: Any) -> List[str]:
    """Schema errors for an ``inventorship_map.json`` payload ([] = valid)."""
    errors: List[str] = []
    if not isinstance(data, dict):
        return ["top level must be a JSON object"]
    elements = data.get("elements")
    if not isinstance(elements, dict) or not elements:
        errors.append("'elements' must be a non-empty object")
        return errors
    prefixes = data.get("vendored_prefixes", [])
    if not isinstance(prefixes, list) or not all(
        isinstance(p, str) for p in prefixes
    ):
        errors.append("'vendored_prefixes' must be a list of strings")
    for key, element in elements.items():
        if not isinstance(element, dict):
            errors.append(f"element {key!r} must be an object")
            continue
        paths = element.get("paths")
        if not isinstance(paths, list) or not paths:
            errors.append(f"element {key!r}: 'paths' must be a non-empty list")
            continue
        for i, entry in enumerate(paths):
            where = f"element {key!r} paths[{i}]"
            if not isinstance(entry, dict):
                errors.append(f"{where} must be an object")
                continue
            if not isinstance(entry.get("path"), str) or not entry.get("path"):
                errors.append(f"{where}: 'path' must be a non-empty string")
            role = entry.get("role", "primary")
            if role not in ROLES:
                errors.append(
                    f"{where}: 'role' must be one of {list(ROLES)}, got {role!r}"
                )
            lines = entry.get("lines")
            if lines is not None and not (
                isinstance(lines, list)
                and len(lines) == 2
                and all(isinstance(n, int) and n > 0 for n in lines)
            ):
                errors.append(
                    f"{where}: 'lines' must be a [start, end] pair of "
                    "positive integers when present"
                )
    return errors


def is_vendored_path(path: str, prefixes: List[str]) -> bool:
    """True when ``path`` falls under a configured vendored prefix."""
    norm = path.lstrip("./")
    return any(norm.startswith(p.lstrip("./")) for p in prefixes if p)


# ---------------------------------------------------------------------------
# collection
# ---------------------------------------------------------------------------


def collect_evidence(
    repo_path: Path,
    map_data: Dict[str, Any],
    *,
    diff_budget: int = DEFAULT_DIFF_BUDGET,
) -> Dict[str, Any]:
    """Mine git history for every mapped path. Deterministic; collection only.

    Returns a result dict with ``evidence`` rows (native schema, all
    ``classification="unclassified"``), ``blame`` summaries for entries
    carrying a ``lines`` range, and ``findings`` (vendored / suspected /
    stale / no-history). Raises :class:`EvidenceError` when git is
    unavailable or ``repo_path`` is not inside a git repository.
    """
    if not check_git_available():
        raise EvidenceError(
            "git is not available on PATH; evidence mining requires git"
        )
    repo = git_toplevel(Path(repo_path))
    if repo is None:
        raise EvidenceError(f"not a git repository: {repo_path}")

    prefixes: List[str] = list(map_data.get("vendored_prefixes", []))
    evidence: List[Dict[str, Any]] = []
    blame_summaries: List[Dict[str, Any]] = []
    findings: List[Dict[str, Any]] = []
    paths_scanned = 0

    for element_key, element in map_data["elements"].items():
        for entry in element["paths"]:
            rel_path: str = entry["path"]
            role: str = entry.get("role", "primary")
            paths_scanned += 1

            # Vendored — BLOCKED, upstream history required, never silent.
            if role == "vendored-primary" or is_vendored_path(rel_path, prefixes):
                findings.append(
                    {
                        "type": FINDING_VENDORED,
                        "element": element_key,
                        "path": rel_path,
                        "detail": (
                            "BLOCKED: vendored path — local git history "
                            "attributes the importer, not the author. "
                            "Upstream history is required for evidence; "
                            "do not mine or pre-fill from this path."
                        ),
                    }
                )
                continue

            # Stale — mapped path no longer on disk. Prompt the operator
            # (or --reseed); NEVER silently update the cached map.
            if not (repo / rel_path).exists():
                findings.append(
                    {
                        "type": FINDING_STALE_PATH,
                        "element": element_key,
                        "path": rel_path,
                        "detail": (
                            "mapped path no longer exists in the repo; "
                            "prompt the operator to confirm the moved/"
                            "renamed location or run --reseed — never "
                            "silently update the cached map."
                        ),
                    }
                )
                continue

            history = path_history(repo, rel_path)
            if not history:
                findings.append(
                    {
                        "type": FINDING_NO_HISTORY,
                        "element": element_key,
                        "path": rel_path,
                        "detail": (
                            "path exists but has zero commits in history "
                            "(uncommitted, or an empty repository); no "
                            "evidence rows mined."
                        ),
                    }
                )
                continue

            # Native bulk-import heuristic on the add-commit.
            added = add_commit(repo, rel_path)
            if added is not None:
                n_files = commit_file_count(repo, added["sha"])
                if n_files > VENDOR_FILE_THRESHOLD and VENDOR_MESSAGE_RE.search(
                    added["subject"]
                ):
                    findings.append(
                        {
                            "type": FINDING_SUSPECTED_VENDORED,
                            "element": element_key,
                            "path": rel_path,
                            "detail": (
                                f"add-commit {added['sha'][:7]} touches "
                                f"{n_files} files (> {VENDOR_FILE_THRESHOLD}) "
                                f"and its message matches the vendor "
                                f"heuristic ({added['subject']!r}); prompt "
                                "the operator before treating local history "
                                "as authorship evidence."
                            ),
                        }
                    )

            for commit in history:
                evidence.append(
                    {
                        "path": rel_path,
                        "sha": commit["sha"],
                        "author": commit["author"],
                        "email": commit["email"],
                        "date": commit["date"],
                        "subject": commit["subject"],
                        "claim_element": element_key,
                        "classification": "unclassified",
                        "rationale": "",
                    }
                )

            lines = entry.get("lines")
            if lines:
                blame = blame_line_range(repo, rel_path, lines[0], lines[1])
                authors: Dict[str, int] = {}
                for b in blame:
                    authors[b["author"]] = authors.get(b["author"], 0) + 1
                blame_summaries.append(
                    {
                        "element": element_key,
                        "path": rel_path,
                        "lines": list(lines),
                        "authors": authors,
                        "shas": sorted({b["sha"] for b in blame}),
                    }
                )

    return {
        "repo": str(repo),
        "generated_at": _utc_now(),
        "diff_budget": diff_budget,
        "elements_scanned": len(map_data["elements"]),
        "paths_scanned": paths_scanned,
        "evidence": evidence,
        "blame": blame_summaries,
        "findings": findings,
    }


def _utc_now() -> str:
    return (
        datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00", "Z"
        )
    )


# ---------------------------------------------------------------------------
# evidence.jsonl (append-only)
# ---------------------------------------------------------------------------


def append_evidence(jsonl_path: Path, rows: List[Dict[str, Any]]) -> int:
    """Append rows to ``evidence.jsonl``, deduped on ``(path, sha, claim_element)``.

    The file is **append-only**: existing rows (including any
    classification/rationale the LLM step wrote back) are never rewritten
    or reordered. Returns the number of rows appended.
    """
    existing = set()
    if jsonl_path.exists():
        for line in jsonl_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            existing.add(tuple(row.get(f) for f in _ROW_KEY_FIELDS))
    appended = 0
    jsonl_path.parent.mkdir(parents=True, exist_ok=True)
    with jsonl_path.open("a", encoding="utf-8") as fh:
        for row in rows:
            key = tuple(row.get(f) for f in _ROW_KEY_FIELDS)
            if key in existing:
                continue
            fh.write(json.dumps(row, sort_keys=True) + "\n")
            existing.add(key)
            appended += 1
    return appended


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point. JSON to stdout; exit 0 clean / 1 findings / 2 error."""
    import argparse
    import sys

    parser = argparse.ArgumentParser(
        prog="inventorship_evidence.py",
        description=(
            "Deterministic git-history evidence mining for the "
            "ip-uspto-inventorship --evidence mode. Collects reduction-"
            "to-practice evidence rows for every path in an "
            "inventorship_map.json; never attributes inventorship "
            "(conception is interview territory)."
        ),
    )
    parser.add_argument(
        "map_path",
        type=Path,
        help="Path to inventorship_map.json (element -> repo paths).",
    )
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path("."),
        help=(
            "Path inside the repository to mine (default: cwd; resolved "
            "to the git toplevel)."
        ),
    )
    parser.add_argument(
        "--write-evidence",
        type=Path,
        default=None,
        metavar="JSONL",
        help=(
            "Append mined rows to this evidence.jsonl (append-only; "
            "deduped on (path, sha, claim_element))."
        ),
    )
    parser.add_argument(
        "--diff-budget",
        type=int,
        default=DEFAULT_DIFF_BUDGET,
        help=(
            "Per-commit diff budget in chars for the downstream "
            f"classification step (default {DEFAULT_DIFF_BUDGET})."
        ),
    )
    args = parser.parse_args(argv)

    try:
        map_data = load_map(args.map_path)
        result = collect_evidence(
            args.repo, map_data, diff_budget=args.diff_budget
        )
    except EvidenceError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.write_evidence is not None:
        result["evidence_appended"] = append_evidence(
            args.write_evidence, result["evidence"]
        )
        result["evidence_jsonl"] = str(args.write_evidence)

    print(json.dumps(result, indent=2))
    return 1 if result["findings"] else 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())


__all__ = [
    "GIT",
    "DEFAULT_DIFF_BUDGET",
    "VENDOR_FILE_THRESHOLD",
    "VENDOR_MESSAGE_RE",
    "ROLES",
    "CLASSIFICATIONS",
    "EVIDENCE_ROW_FIELDS",
    "FINDING_VENDORED",
    "FINDING_SUSPECTED_VENDORED",
    "FINDING_STALE_PATH",
    "FINDING_NO_HISTORY",
    "EvidenceError",
    "check_git_available",
    "git_toplevel",
    "path_history",
    "add_commit",
    "commit_file_count",
    "commit_diff",
    "blame_line_range",
    "load_map",
    "validate_map",
    "is_vendored_path",
    "collect_evidence",
    "append_evidence",
    "main",
]
