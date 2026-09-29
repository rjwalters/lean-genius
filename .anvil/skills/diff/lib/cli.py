#!/usr/bin/env python3
"""Runnable CLI entry point for `anvil:diff` (issue #925).

``commands/diff.md`` documents the flow as "one library call per mode" --
but per the ``project-share`` precedent (issue #755), there is no
runnable path to a skill-local ``lib/`` package short of a script that
does its own ``importlib`` bootstrap: the package needs the repo root on
``sys.path`` before ``anvil.lib.skill_lib_loader`` (itself under
``anvil.lib``) is importable, and this skill's ``lib/`` modules use
relative imports (``from .sources import ...``) so they must be loaded as
a package, not as loose modules.

Runnable as::

    python3 .anvil/anvil/skills/diff/lib/cli.py versions <thread-dir> <slug>
    python3 .anvil/anvil/skills/diff/lib/cli.py deslop <thread-dir> --origin <path>
    python3 .anvil/anvil/skills/diff/lib/cli.py files <left> <right>

(from a consumer install; from the anvil source repo the path is
``anvil/skills/diff/lib/cli.py``).

Read-only over every INPUT path in all three modes -- the only path this
CLI ever writes to is ``--out`` (an operator-chosen NEW output path), and
only when that flag is passed. The default behavior (serve, or
``--no-serve`` with no ``--out``) writes nothing to disk at all.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from types import ModuleType
from typing import Optional

_PACKAGE_NAME = "diff_lib"
# Dependency-safe load order: sources and overlay have no intra-package
# dependency on each other; server has none either. Listed in the order
# a reader would want them introduced.
_MODULES = ["sources", "overlay", "server"]


def _bootstrap_sys_path() -> None:
    """Make ``import anvil`` resolvable when run as a bare script.

    Byte-identical, intentionally duplicated copy of the algorithm in
    ``anvil.lib.skill_lib_loader.bootstrap_sys_path`` — a bootstrap that
    makes ``anvil`` importable can't itself import from ``anvil`` yet, so
    this can't just delegate to it (issue #1100). See that function's
    docstring for the full layout-resolution explanation, and
    ``tests/lib/test_bootstrap_sys_path_consistency.py`` for the check
    that keeps this copy honest.
    """

    here = Path(__file__).resolve()
    for ancestor in here.parents:
        if (ancestor / "anvil" / "__init__.py").is_file():
            if str(ancestor) not in sys.path:
                sys.path.insert(0, str(ancestor))
            return


def _load_lib() -> ModuleType:
    """Load this skill's ``lib/`` package and return it (with submodules
    bound as attributes: ``.sources``, ``.overlay``, ``.server``)."""

    _bootstrap_sys_path()
    from anvil.lib.skill_lib_loader import load_skill_lib

    lib_dir = Path(__file__).resolve().parent
    ns = load_skill_lib("diff", lib_dir, _MODULES, package_name=_PACKAGE_NAME)
    return ns


FRAMEWORK_IMPORT_REMEDIATION = (
    "diff cli: could not import the anvil framework (anvil.lib.*). In a "
    "consumer install, run `uv sync --project .anvil` once, then "
    "re-invoke as `uv run --project .anvil python "
    ".anvil/anvil/skills/diff/lib/cli.py <mode> ...`."
)


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--left-label", default=None, help="Override the left-pane label."
    )
    parser.add_argument(
        "--right-label", default=None, help="Override the right-pane label."
    )
    parser.add_argument(
        "--lint",
        choices=["left", "right", "both", "none"],
        default="right",
        help=(
            "Which side(s) to run the deterministic rhetoric lint over "
            "and overlay inline (default: right -- the newer/revised "
            "side, the natural target for polishing)."
        ),
    )
    parser.add_argument(
        "--port",
        type=int,
        default=0,
        help="TCP port to bind (default: 0, an OS-assigned ephemeral port).",
    )
    parser.add_argument(
        "--no-serve",
        action="store_true",
        help=(
            "Do not start the localhost server; print the rendered HTML "
            "to stdout instead (or write it via --out)."
        ),
    )
    parser.add_argument(
        "--out",
        default=None,
        help=(
            "Also write the rendered HTML to this path. This is the ONLY "
            "path anvil:diff ever writes to -- an operator-chosen new "
            "output location, never an input path."
        ),
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="cli.py",
        description=(
            "Local, read-only, word-level side-by-side prose diff viewer. "
            "See commands/diff.md for the full procedure."
        ),
    )
    sub = parser.add_subparsers(dest="mode", required=True)

    p_versions = sub.add_parser(
        "versions",
        help="Diff two {slug}.{N} version dirs under thread_dir.",
    )
    p_versions.add_argument(
        "thread_dir", help="Portfolio directory containing {slug}.{N}/ dirs."
    )
    p_versions.add_argument("slug", help="Thread slug, e.g. 'acme-seed'.")
    p_versions.add_argument(
        "--from",
        dest="from_n",
        type=int,
        default=None,
        help="Older version N (default: the version just before --to).",
    )
    p_versions.add_argument(
        "--to",
        dest="to_n",
        type=int,
        default=None,
        help="Newer version N (default: the .latest-resolved version).",
    )
    p_versions.add_argument(
        "--no-review-overlay",
        action="store_true",
        help="Skip the .review/ sidecar overlay even when present.",
    )
    _add_common_args(p_versions)

    p_deslop = sub.add_parser(
        "deslop",
        help="Diff a deslop origin file against its emit/cleaned.txt.",
    )
    p_deslop.add_argument(
        "thread_dir", help="Deslop scratch thread dir (contains emit/)."
    )
    p_deslop.add_argument(
        "--origin", required=True, help="Path to the original source file."
    )
    _add_common_args(p_deslop)

    p_files = sub.add_parser("files", help="Diff two arbitrary files.")
    p_files.add_argument("left", help="Path to the 'before' file.")
    p_files.add_argument("right", help="Path to the 'after' file.")
    _add_common_args(p_files)

    return parser


def _rationale_notes(rationale_path: Optional[Path], overlay: ModuleType) -> list:
    """Deslop rationale.md -> a flat list of unanchored OverlayNote.

    ``emit()`` writes rationale as a plain bullet list with no per-hunk
    anchor (see ``anvil/skills/deslop/lib/orchestrate.py::emit``), so
    these render as document-level notes rather than line-anchored ones
    -- an honest reflection of what the underlying data carries.
    """

    from anvil.lib.prose_diff import OverlayNote

    if rationale_path is None:
        return []
    notes = []
    for line in rationale_path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("- "):
            notes.append(
                OverlayNote(
                    line=None,
                    severity="info",
                    message=stripped[2:].strip(),
                    source="deslop:rationale",
                )
            )
    return notes


def main(argv: Optional[list] = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        lib = _load_lib()
    except ImportError:
        print(FRAMEWORK_IMPORT_REMEDIATION, file=sys.stderr)
        return 1

    from anvil.lib.prose_diff import diff_prose, render_html

    sources = lib.sources
    overlay = lib.overlay
    server = lib.server

    left_overlay: list = []
    right_overlay: list = []
    rationale_notes: list = []

    try:
        if args.mode == "versions":
            thread_dir = Path(args.thread_dir)
            from_path, to_path = sources.resolve_version_pair(
                thread_dir, args.slug, from_n=args.from_n, to_n=args.to_n
            )
            left_file = sources.resolve_body_file(from_path, args.slug)
            right_file = sources.resolve_body_file(to_path, args.slug)
            if left_file is None:
                raise sources.VersionPairError(
                    f"could not find a body file inside {from_path}"
                )
            if right_file is None:
                raise sources.VersionPairError(
                    f"could not find a body file inside {to_path}"
                )
            left_label = args.left_label or from_path.name
            right_label = args.right_label or to_path.name
            if not args.no_review_overlay:
                left_overlay += overlay.load_review_overlay(from_path)
                right_overlay += overlay.load_review_overlay(to_path)

        elif args.mode == "deslop":
            thread_dir = Path(args.thread_dir)
            origin, cleaned, rationale = sources.resolve_deslop_pair(
                thread_dir, Path(args.origin)
            )
            left_file, right_file = origin, cleaned
            left_label = args.left_label or "origin"
            right_label = args.right_label or "cleaned"
            rationale_notes = _rationale_notes(rationale, overlay)

        else:  # files
            left_file, right_file = Path(args.left), Path(args.right)
            if not left_file.is_file():
                raise sources.VersionPairError(f"file not found: {left_file}")
            if not right_file.is_file():
                raise sources.VersionPairError(f"file not found: {right_file}")
            left_label = args.left_label or left_file.name
            right_label = args.right_label or right_file.name

    except sources.VersionPairError as exc:
        print(f"diff cli: {exc}", file=sys.stderr)
        return 1

    left_text = _read_text(left_file)
    right_text = _read_text(right_file)

    if args.lint in ("left", "both"):
        left_overlay += overlay.load_rhetoric_lint_overlay(left_text)
    if args.lint in ("right", "both"):
        right_overlay += overlay.load_rhetoric_lint_overlay(right_text)
    right_overlay += rationale_notes

    result = diff_prose(left_text, right_text)
    page = render_html(
        result,
        left_label=left_label,
        right_label=right_label,
        title=f"anvil:diff -- {left_label} vs {right_label}",
        left_overlay=left_overlay or None,
        right_overlay=right_overlay or None,
    )

    if args.out:
        Path(args.out).write_text(page, encoding="utf-8")
        print(f"wrote {args.out}")

    if args.no_serve:
        if not args.out:
            print(page)
        return 0

    httpd = server.build_server(page, port=args.port)
    server.serve_until_interrupt(httpd)
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())


__all__ = ["FRAMEWORK_IMPORT_REMEDIATION", "main"]
