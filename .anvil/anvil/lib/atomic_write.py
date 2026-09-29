"""Atomic file-level writes via tmp-sibling + ``os.replace`` (issue #1104).

The "write to a ``.tmp`` sibling file in the same directory, then
``os.replace()`` over the destination" primitive was independently
reimplemented at least 8 times across the codebase — three of those
duplicates even carried a comment naming this exact spot as the
would-be canonical home and never imported it. This module is that
canonical home.

This is the **file**-level analog of :mod:`anvil.lib.sidecar`'s
directory-level staging-then-rename primitive (issue #350) — that
module handles fan-in of N files into one critic-sibling directory;
this one handles a single file's own tmp-then-rename swap. Both rely
on the same POSIX guarantee: ``os.replace()`` is atomic on a given
filesystem, so the destination path is never observed holding partial
content.

Public API:

- :func:`atomic_write_text` — write a string, any encoding.
- :func:`atomic_write_bytes` — write raw bytes.
- :func:`atomic_write_json` — serialize + write JSON (``indent=2`` +
  trailing newline, the on-disk convention already used by every
  consolidated call site).
- :func:`atomic_replace` — the bare tmp-to-destination swap, for a
  caller whose tmp file is populated by something other than a Python
  ``write_text``/``write_bytes`` call (e.g. a subprocess rendering
  directly into the tmp path). The three write helpers above call this
  internally once their tmp sibling is populated.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any


def atomic_replace(tmp_path: Path, dest_path: Path) -> None:
    """Atomically replace ``dest_path`` with the already-populated ``tmp_path``.

    Thin, named wrapper around ``os.replace()`` — the second half of the
    tmp-then-replace pattern, split out for callers that populate their
    own tmp file directly (e.g. redirecting a subprocess's output there)
    rather than through :func:`atomic_write_bytes` / `_text` / `_json`.
    """
    os.replace(Path(tmp_path), Path(dest_path))


def atomic_write_bytes(path: Path, data: bytes) -> None:
    """Write ``data`` to ``path`` atomically (tmp sibling + ``os.replace``).

    Writes to a ``<name>.tmp`` sibling in the same directory as ``path``
    first, then ``os.replace()``s it into place, so ``path`` is never
    observed holding partial content. The tmp sibling lives in the same
    directory (not a system temp dir) so the final rename is guaranteed
    to be same-filesystem and therefore atomic.
    """
    path = Path(path)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_bytes(data)
    atomic_replace(tmp, path)


def atomic_write_text(path: Path, text: str, *, encoding: str = "utf-8") -> None:
    """Write ``text`` to ``path`` atomically (tmp sibling + ``os.replace``).

    See :func:`atomic_write_bytes` for the atomicity contract.
    """
    atomic_write_bytes(Path(path), text.encode(encoding))


def atomic_write_json(path: Path, data: Any, *, indent: int = 2) -> None:
    """Serialize ``data`` to JSON and atomic-write it to ``path``.

    Uses ``indent=2`` plus a trailing newline by default — the on-disk
    convention already shared by every consolidated call site. Pass
    ``indent=None`` for compact JSON if a caller ever needs it.
    """
    atomic_write_text(path, json.dumps(data, indent=indent) + "\n")


__all__ = [
    "atomic_replace",
    "atomic_write_bytes",
    "atomic_write_text",
    "atomic_write_json",
]
