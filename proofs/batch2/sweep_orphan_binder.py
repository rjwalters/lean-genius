#!/usr/bin/env python3
"""Repo-wide sweep for two v4.31 mechanical classes (batch 4):
  1. trailing orphaned doc-comment: /-- ... -/ followed (through trivia) only by
     `end ...` or EOF -> demote to /- ... -/
  2. double set-binder: (∀|∃) x y ∈ S, -> split into two binders
Applies only to files in the candidate list (inventory FAIL minus already GREEN).
Prints TSV: file<TAB>class per applied fix.  --dry-run to scan only.
"""
import re, sys, pathlib

DRY = "--dry-run" in sys.argv
ROOT = pathlib.Path("/Users/rwalters/GitHub/lean-genius/.loom/worktrees/epic-37508/proofs/Proofs")

def load_candidates():
    fails = set()
    for line in open(ROOT.parent / "spike-logs-full/results-full.tsv"):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 2 and parts[1] == "FAIL":
            fails.add(parts[0])
    green = set()
    for line in open(ROOT.parent / "batch2/verify-results.tsv"):
        parts = line.rstrip("\n").split("\t")
        if len(parts) >= 2 and parts[1] == "GREEN":
            green.add(parts[0])
    return fails - green

def find_orphan_docs(text):
    """Return list of (start_offset) of /-- blocks that are trailing-orphaned."""
    hits = []
    i, n = 0, len(text)
    # collect all block comments with nesting, note doc (/--) vs plain
    while i < n:
        if text.startswith("/-", i):
            is_doc = text.startswith("/--", i) and not text.startswith("/--/", i)
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            end = j
            if is_doc:
                # scan forward through trivia: whitespace, line comments, block comments
                k = end
                orphan = None
                while True:
                    while k < n and text[k] in " \t\n\r":
                        k += 1
                    if k >= n:
                        orphan = True; break
                    if text.startswith("--", k):
                        nl = text.find("\n", k)
                        k = n if nl == -1 else nl + 1
                        continue
                    if text.startswith("/-", k):
                        d, m = 1, k + 2
                        while m < n and d:
                            if text.startswith("/-", m): d += 1; m += 2
                            elif text.startswith("-/", m): d -= 1; m += 2
                            else: m += 1
                        k = m
                        continue
                    # real token
                    orphan = bool(re.match(r"end\b", text[k:]))
                    break
                if orphan:
                    hits.append(i)
            i = end
        elif text.startswith("--", i):
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        else:
            i += 1
    return hits

BINDER_RE = re.compile(r"([∀∃])\s*(\w+)\s+(\w+)\s+∈\s+([^,{}\n]+?),")

def fix_binders(text):
    count = 0
    def repl(m):
        nonlocal count
        q, a, b, s = m.groups()
        count += 1
        return f"{q} {a} ∈ {s}, {q} {b} ∈ {s},"
    new = BINDER_RE.sub(repl, text)
    return new, count

def main():
    cands = load_candidates()
    touched = []
    for name in sorted(cands):
        p = ROOT / f"{name}.lean"
        if not p.exists():
            continue
        text = p.read_text()
        orig = text
        classes = []
        # orphan doc fix: replace from the end to keep offsets valid
        hits = find_orphan_docs(text)
        if hits:
            for off in reversed(hits):
                assert text.startswith("/--", off)
                text = text[:off] + "/-" + text[off + 3:]
            classes.append(f"orphan-doc x{len(hits)}")
        # double-binder rewriting disabled: regex hits prose inside comments;
        # the 5 real code sites were fixed by hand (batch 4).
        if text != orig:
            if not DRY:
                p.write_text(text)
            for c in classes:
                print(f"{name}\t{c}")
            touched.append(name)
    print(f"# touched {len(touched)} files", file=sys.stderr)

main()
