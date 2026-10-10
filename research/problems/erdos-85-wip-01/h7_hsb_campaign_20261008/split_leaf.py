#!/usr/bin/env python3
"""Split hard hsb3 leaves into sub-leaves plus one sub-cover (README section 9).

For a leaf (cube, n) the generator builds a lookahead cube tree of depth <= D over the PRIMARY
variables (the 861 edge variables of the vertices 7..48, DIMACS 1..861) of the leaf CNF:

  * at a node, every free primary variable v is probed v = true and v = false by unit propagation
    from the node's assignment (leaf units + decisions + everything forced so far);
  * a probe that ends in a conflict is a failed literal: the opposite literal is forced at this node
    (it is implied, so no model is lost) and the round is repeated; both sides failing refutes the node;
  * otherwise the variable with the largest (pT + 1) * (pF + 1) is chosen (p = number of variables the
    probe assigned; ties: smallest variable), the positive branch first;
  * a node refuted by unit propagation or failed literals is OMITTED: no model of the leaf CNF reaches
    it, so the remaining cubes still cover every model;
  * a node at depth D becomes a cube (its decision literals in tree order).

Each cube l_1 .. l_k gives the blocking clause c = [-l_1, ..., -l_k]. Lean
(`sevenHighT0CanonicalHsbLeafChecked_of_split`) needs, for the blocking list B = [c_0, c_1, ...]:

  sub-leaf i  = leaf CNF ++ cnfClauseNegUnits c_i   (units l_1 .. l_k, in order)  UNSAT, for every i
  sub-cover   = leaf CNF ++ cnfOfClauseList B       (every c_i verbatim, in order) UNSAT

The blocking clauses are arbitrary for soundness: the checked sub-cover alone vouches for them, so
neither the lookahead nor this generator is trusted. Determinism matters only for reproducibility:
the split is a pure function of the pinned inputs (inputs.json), the leaf index and D.

    split_leaf.py --inputs DIR --leaf cube_F9_t0:1 --leaf cube_F8_t0:4 --depth 6 --out m.jsonl --specs s.jsonl
    split_leaf.py --inputs DIR --leaves-file residual-pass-manifest.jsonl --depth 6 --out m.jsonl --jobs 6

Manifest rows (one JSON object per line, sorted keys; ids contain no '.'):
  {"id": "<cube>-s<leaf:05d>-<sha8>-cover", "kind": "subcover", "cube", "leaf", "split_sha256", "subleaves", "clauses", "cnf_sha256"}
  {"id": "<cube>-s<leaf:05d>-<sha8>-<i:03d>", "kind": "subleaf", "cube", "leaf", "split_sha256", "index", "subleaves", "clause", "cnf_sha256"}
(<sha8> = the first 8 hex digits of split_sha256.) `split_sha256` = h7_common.split_sha256(cube, leaf, leaf CNF sha256, B); `cnf_sha256` is computed
from the pinned inputs without writing the CNF (the worker recomputes it and also hashes the file).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import h7_common as hc  # noqa: E402

PRIMARY_VARIABLES = 861  # C(42, 2): edges among the vertices 7..48 (edgeVar j v, j < 41)
METHOD = ("lookahead-v1: primary vars 1..861; probe both signs by unit propagation; failed literals forced; "
          "score (pT+1)*(pF+1), ties smallest var; positive branch first; UP/failed-literal-refuted nodes omitted")
REFUTED = object()


class Engine:
    """Unit propagation over cube ++ hsb of one cube (parsed once), with a trail for undo."""

    def __init__(self, cube: hc.Cube):
        self.cube = cube
        n = hc.VARIABLES
        self.clauses: list[tuple[int, ...]] = []
        occ: list[list[int]] = [[] for _ in range(2 * n + 1)]
        for line in cube.body.splitlines():
            lits = tuple(int(t) for t in line.split()[:-1])
            idx = len(self.clauses)
            self.clauses.append(lits)
            for x in lits:
                occ[x + n].append(idx)
        self.occ = occ
        self.n = n

    # ---- assignment state --------------------------------------------------------------------
    def reset(self, units: list[int]) -> bool:
        self.val = [0] * (self.n + 1)
        self.trail: list[int] = []
        for cl in self.clauses:  # unit clauses of cube ++ hsb
            if len(cl) == 1 and not self._push(cl[0]):
                return False
        for u in units:
            if not self._push(u):
                return False
        return self._propagate(0)

    def _push(self, lit: int) -> bool:
        v = abs(lit)
        s = 1 if lit > 0 else -1
        if self.val[v] == s:
            return True
        if self.val[v] == -s:
            return False
        self.val[v] = s
        self.trail.append(lit)
        return True

    def _propagate(self, head: int) -> bool:
        val, clauses, occ, n, trail = self.val, self.clauses, self.occ, self.n, self.trail
        while head < len(trail):
            lit = trail[head]
            head += 1
            for ci in occ[n - lit]:
                unit = 0
                free = 0
                for x in clauses[ci]:
                    a = val[x if x > 0 else -x]
                    if a == 0:
                        free += 1
                        if free > 1:
                            break
                        unit = x
                    elif (a > 0) == (x > 0):
                        free = 2  # satisfied
                        break
                if free == 0:
                    return False
                if free == 1:
                    val[unit if unit > 0 else -unit] = 1 if unit > 0 else -1
                    trail.append(unit)
        return True

    def undo(self, mark: int) -> None:
        val, trail = self.val, self.trail
        while len(trail) > mark:
            val[abs(trail.pop())] = 0

    def assume(self, lit: int) -> bool:
        """Assign lit and propagate. On conflict the caller undoes to its own mark."""
        mark = len(self.trail)
        if not self._push(lit):
            return False
        return self._propagate(mark)

    def probe(self, lit: int) -> int:
        mark = len(self.trail)
        ok = self.assume(lit)
        count = len(self.trail) - mark
        self.undo(mark)
        return count if ok else -1

    # ---- lookahead -----------------------------------------------------------------------------
    def choose(self):
        """Failed-literal rounds, then the best split variable. Forced literals stay on the trail
        (the caller undoes them with the node). Returns REFUTED, None (no free primary variable) or v."""
        while True:
            best, best_score, changed = None, -1, False
            for v in range(1, PRIMARY_VARIABLES + 1):
                if self.val[v]:
                    continue
                pt, pf = self.probe(v), self.probe(-v)
                if pt < 0 and pf < 0:
                    return REFUTED
                if pt < 0 or pf < 0:
                    if not self.assume(-v if pt < 0 else v):
                        return REFUTED
                    changed = True
                    continue
                score = (pt + 1) * (pf + 1)
                if score > best_score:
                    best, best_score = v, score
            if not changed:
                return best

    def tree(self, depth: int, prefix: list[int], stats: dict) -> list[list[int]]:
        if depth == 0:
            return [prefix]
        mark = len(self.trail)
        stats["nodes"] += 1
        r = self.choose()
        if r is REFUTED:
            stats["refuted"] += 1
            self.undo(mark)
            return []
        if r is None:
            self.undo(mark)
            return [prefix]
        out: list[list[int]] = []
        for lit in (r, -r):
            m2 = len(self.trail)
            if self.assume(lit):
                out += self.tree(depth - 1, prefix + [lit], stats)
            else:
                stats["refuted"] += 1
            self.undo(m2)
        self.undo(mark)
        return out


def split(engine: Engine, leaf: int, depth: int) -> dict:
    """The split of one leaf: blocking clauses and the split sha256 (deterministic)."""
    cube = engine.cube
    if not 1 <= depth <= 10:
        raise ValueError("depth must be 1..10")
    if not engine.reset(cube.units(leaf)):
        raise ValueError(f"{cube.name} leaf {leaf}: unit propagation refutes the leaf; no split needed")
    stats = {"nodes": 0, "refuted": 0, "root_assigned": len(engine.trail)}
    cubes = engine.tree(depth, [], stats)
    if not cubes or cubes == [[]]:
        raise ValueError(f"{cube.name} leaf {leaf}: split produced no cube ({stats})")
    clauses = [[-l for l in c] for c in cubes]
    leaf_sha = cube.leaf_sha256(leaf)
    return {"schema": hc.SPLIT_SCHEMA, "cube": cube.name, "leaf": leaf, "leaf_cnf_sha256": leaf_sha, "depth": depth,
            "method": METHOD, "clauses": clauses, "split_sha256": hc.split_sha256(cube.name, leaf, leaf_sha, clauses),
            "subleaves": len(clauses), "stats": stats}


def rows_of(cube: hc.Cube, spec: dict) -> list[dict]:
    """Manifest rows of one split: the sub-cover first, then the sub-leaves in blocking-list order."""
    leaf, clauses, sha = spec["leaf"], spec["clauses"], spec["split_sha256"]
    assert hc.split_sha256(cube.name, leaf, cube.leaf_sha256(leaf), clauses) == sha
    base = {"cube": cube.name, "leaf": leaf, "split_sha256": sha, "subleaves": len(clauses)}
    stem = f"{cube.name}-s{leaf:05d}-{sha[:8]}"  # the split sha in the id: a re-split of a leaf never reuses a claim
    rows = [dict(base, id=f"{stem}-cover", kind="subcover", clauses=clauses, cnf_sha256=cube.subcover_sha256(leaf, clauses))]
    for i, c in enumerate(clauses):
        rows.append(dict(base, id=f"{stem}-{i:03d}", kind="subleaf", index=i, clause=c, cnf_sha256=cube.subleaf_sha256(leaf, c)))
    return rows


def manifest_bytes(rows: list[dict]) -> bytes:
    return "".join(json.dumps(r, sort_keys=True) + "\n" for r in rows).encode()


def parse_leaves(a) -> list[tuple[str, int]]:
    out = []
    for s in a.leaf:
        name, _, n = s.partition(":")
        out.append((name, int(n)))
    if a.leaves_file:
        for line in Path(a.leaves_file).read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            if line.startswith("{"):  # a residual manifest row (one leaf per row) or {"cube":..,"leaf":..}
                r = json.loads(line)
                for n in (r["leaves"] if "leaves" in r else [r["leaf"]]):
                    out.append((r["cube"], int(n)))
            else:
                name, n = line.split()
                out.append((name, int(n)))
    bad = sorted({c for c, _ in out} - set(hc.CUBES))
    if bad:
        raise SystemExit(f"unknown cube(s): {bad}")
    seen, uniq = set(), []
    for x in out:
        if x not in seen:
            seen.add(x)
            uniq.append(x)
    order = {c: i for i, c in enumerate(hc.CUBES)}
    return sorted(uniq, key=lambda x: (order[x[0]], x[1]))


def _work(args: tuple) -> list[dict]:
    inputs, name, leaves, depth = args
    cube = hc.Cube(Path(inputs), name)
    eng = Engine(cube)
    return [split(eng, n, depth) for n in leaves]


def generate(inputs: Path, leaves: list[tuple[str, int]], depth: int, jobs: int = 1) -> tuple[list[dict], list[dict]]:
    """Specs and manifest rows for the given leaves, in (cube order, leaf) order regardless of jobs."""
    by_cube: dict[str, list[int]] = {}
    for c, n in leaves:
        by_cube.setdefault(c, []).append(n)
    tasks = []
    for c, ns in by_cube.items():  # chunks of 8 leaves so that --jobs parallelises inside a big cube
        for k in range(0, len(ns), 8):
            tasks.append((str(inputs), c, ns[k:k + 8], depth))
    if jobs > 1:
        import multiprocessing as mp
        with mp.get_context("spawn").Pool(jobs) as pool:
            results = pool.map(_work, tasks)
    else:
        results = [_work(t) for t in tasks]
    specs = [s for r in results for s in r]
    order = {c: i for i, c in enumerate(hc.CUBES)}
    specs.sort(key=lambda s: (order[s["cube"]], s["leaf"]))
    rows, cubes = [], {}
    for s in specs:
        cube = cubes.get(s["cube"]) or cubes.setdefault(s["cube"], hc.Cube(inputs, s["cube"]))
        rows += rows_of(cube, s)
    return specs, rows


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--inputs", type=Path, required=True)
    p.add_argument("--leaf", action="append", default=[], help="cube:index (repeatable)")
    p.add_argument("--leaves-file", help="lines 'cube index', or JSON rows with cube + leaves/leaf (e.g. a residual manifest)")
    p.add_argument("--depth", type=int, default=6)
    p.add_argument("--out", type=Path, help="manifest (jsonl)")
    p.add_argument("--specs", type=Path, help="split specs with stats (jsonl)")
    p.add_argument("--jobs", type=int, default=1)
    p.add_argument("--inputs-sha256", default="", help="require this sha256 of inputs.json")
    a = p.parse_args()
    got = hc.sha_file(a.inputs / "inputs.json")
    if a.inputs_sha256 and got != a.inputs_sha256:
        raise SystemExit(f"inputs.json sha256 {got} != {a.inputs_sha256}")
    leaves = parse_leaves(a)
    if not leaves:
        raise SystemExit("no leaves given")
    specs, rows = generate(a.inputs, leaves, a.depth, a.jobs)
    gen = {"split_leaf_py_sha256": hc.sha_file(Path(__file__)), "h7_common_py_sha256": hc.sha_file(HERE / "h7_common.py"),
           "inputs_json_sha256": got}
    raw = manifest_bytes(rows)
    if a.out:
        a.out.write_bytes(raw)
    if a.specs:
        a.specs.write_text("".join(json.dumps(dict(s, generator=gen), sort_keys=True) + "\n" for s in specs))
    print(json.dumps({"leaves": len(specs), "depth": a.depth, "rows": len(rows),
                      "subleaves": sum(s["subleaves"] for s in specs),
                      "subleaves_per_leaf": [s["subleaves"] for s in specs][:40],
                      "manifest_sha256": hashlib.sha256(raw).hexdigest(), **gen}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
