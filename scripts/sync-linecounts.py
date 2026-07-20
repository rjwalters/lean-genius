#!/usr/bin/env python3
"""Sync stale ``lineCount`` fields in gallery meta.json to the real ``wc -l``.

Fixes the systemic ``leanFile.lineCount`` drift documented in issue #39452
(~1,325 of 3,348 entries stale after the v4.31 toolchain flip #39062, whose
follow-up meta sweep #39063 only touched ``mathlib_version``). This is the same
class of bulk fix as #35927 (theoremCount/definitionCount resync).

Only three pointers track the primary Lean file and are resynced:

    /meta/lineCount        (nested "meta" block)
    /leanFile/lineCount    (top-level leanFile block)
    /lineCount             (rare top-level scalar)

Every other ``lineCount`` — ``additionalFiles[]``, ``leanFiles[]``,
``companionFiles[]`` — references a *companion* file, not the primary, and is
left untouched. Section ``startLine``/``endLine`` ranges also drift but require
content-anchored remapping (see #39450) and are explicitly out of scope here.

The edit is surgical: only the integer value on the target ``lineCount`` line is
rewritten, preserving each file's exact formatting (compact string arrays, etc.).
Every rewrite is verified by re-parsing the result and asserting that no other
``lineCount`` pointer changed; a file that fails verification is skipped and
reported.

Usage:
    python3 scripts/sync-linecounts.py            # apply
    python3 scripts/sync-linecounts.py --dry-run  # report only
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOFS_DIR = os.path.join(REPO_ROOT, "proofs")
GLOB = os.path.join(REPO_ROOT, "src", "data", "proofs", "*", "meta.json")

OPEN_KEYED = re.compile(r'^\s*"([A-Za-z0-9_]+)":\s*\{\s*$')
OPEN_ANON = re.compile(r"^\s*\{\s*$")
LINECOUNT = re.compile(r'^(\s*"lineCount":\s*)(\d+)(,?\s*)$')
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')  # a complete JSON string literal


def _structural(line: str) -> str:
    """Blank out string literals so brace counting ignores braces in values.

    Meta.json is pretty-printed, so every string literal is contained on one
    line; masking them makes ``{``/``}`` counts reflect real object nesting even
    when a description contains LaTeX/set-notation braces."""
    return STRING.sub('""', line)

# JSON pointers that track the primary Lean file (see module docstring).
PRIMARY_PTRS = ("/leanFile/lineCount", "/meta/lineCount", "/lineCount")


def wc_l(path: str) -> "int | None":
    f = os.path.join(PROOFS_DIR, path)
    if not os.path.isfile(f):
        return None
    with open(f, "rb") as fh:
        return fh.read().count(b"\n")


def all_linecount_pointers(obj, ptr="") -> dict:
    """Map every lineCount JSON pointer -> value (arrays collapse to '/[]')."""
    out = {}
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k == "lineCount" and isinstance(v, int):
                out[ptr + "/lineCount"] = v
            out.update(all_linecount_pointers(v, ptr + "/" + k))
    elif isinstance(obj, list):
        for v in obj:
            out.update(all_linecount_pointers(v, ptr + "/[]"))
    return out


def rewrite(raw: str, target: int) -> str:
    """Rewrite lineCount at /meta, /leanFile, and top-level to ``target``.

    Object depth is tracked by counting braces; the key that opened each object
    level is tracked so only the three primary-tracking pointers are touched.
    Files are pretty-printed (only string arrays are ever inline), so braces
    reliably delimit object nesting.
    """
    lines = raw.splitlines(keepends=True)
    key_stack = []  # keys of currently-open objects; outermost is "root"
    out = []
    for line in lines:
        m = LINECOUNT.match(line)
        if m and key_stack:
            top = key_stack[-1]
            depth = len(key_stack)
            is_target = (
                (depth == 1 and top == "root")            # top-level /lineCount
                or (depth == 2 and top in ("meta", "leanFile"))
            )
            if is_target:
                line = f"{m.group(1)}{target}{m.group(3)}"
        out.append(line)

        # Update structural state AFTER emitting the line.
        km = OPEN_KEYED.match(line)
        if km:
            key_stack.append(km.group(1))
            continue
        if OPEN_ANON.match(line):
            # the outermost "{" is the root object; deeper ones are array elements
            key_stack.append("root" if not key_stack else None)
            continue
        struct = _structural(line)
        opens = struct.count("{")
        closes = struct.count("}")
        if opens:
            # opening brace(s) not matched by the keyed/anon patterns (e.g. an
            # inline "{...}"); track net depth conservatively.
            for _ in range(opens):
                key_stack.append("root" if not key_stack else None)
        for _ in range(closes):
            if key_stack:
                key_stack.pop()
    return "".join(out)


def main() -> int:
    dry = "--dry-run" in sys.argv
    changed = failed = 0
    fail_files = []
    for meta_path in sorted(glob.glob(GLOB)):
        raw = open(meta_path, encoding="utf-8").read()
        try:
            d = json.loads(raw)
        except json.JSONDecodeError:
            continue
        lf = d.get("leanFile")
        if not isinstance(lf, dict) or not lf.get("path"):
            continue
        target = wc_l(lf["path"])
        if target is None:
            continue

        before = all_linecount_pointers(d)
        primary_ptrs = [p for p in PRIMARY_PTRS if p in before]
        if all(before[p] == target for p in primary_ptrs):
            continue

        new_raw = rewrite(raw, target)
        if new_raw == raw:
            continue

        # Verify: re-parse and confirm ONLY the intended pointers changed.
        try:
            nd = json.loads(new_raw)
        except json.JSONDecodeError:
            failed += 1
            fail_files.append((meta_path, "reparse"))
            continue
        after = all_linecount_pointers(nd)
        ok = set(before) == set(after)
        for p in after:
            want = target if p in PRIMARY_PTRS else before[p]
            if after[p] != want:
                ok = False
        if not ok:
            failed += 1
            fail_files.append((meta_path, "pointer-mismatch"))
            continue

        if dry:
            print(f"WOULD FIX {os.path.basename(os.path.dirname(meta_path))}: "
                  f"{[before[p] for p in primary_ptrs]} -> {target}")
        else:
            with open(meta_path, "w", encoding="utf-8") as fh:
                fh.write(new_raw)
        changed += 1

    print(f"\n{'(dry-run) ' if dry else ''}fixed={changed} failed-verify={failed}")
    for f, why in fail_files:
        print(f"  FAILED[{why}]: {f}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
