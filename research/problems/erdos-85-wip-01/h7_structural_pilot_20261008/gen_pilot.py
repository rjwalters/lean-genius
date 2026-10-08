#!/usr/bin/env python3
"""Emit H7/T0 structural-cube CNFs, optionally strengthened by extra clauses.

Base: the compact canonical cube CNF (17,633 vars, 720,825 clauses), byte-checked
against the frozen root hashes in h7-frontier-map-20260915/results.json.  The Lean
term is `orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i`; extra clauses are
appended AFTER the cube (matching `...EmptyCubeExtraSatCnf = cube ++ extra`).

Extra-clause families (comma-separated --facts):
  cap   singleton <= 2 empty nbrs, pair-vertex <= 1 empty nbr  (edge-only)
  fp    forbidden-pair: empties with a common EMPTY nbr share no outside nbr (edge-only;
        expected redundant: it is a binary C4 clause after the 21 cube units)
  x35   |exterior-pair graph on E| >= 35 - 4a (aux vars: witnesses + seq counter)
  dlex  lex-leader x <=lex g(x) for every non-identity g in the DIAGONAL S7 stabilizer
        of the mask (the group already formalized in ...CanonicalEmptyStabilizerLex)
  hsbK  NEW: high-side symmetry breaking.  The group S7(highs) x| (Z/2)^7 (singleton
        copy swaps), acting on highs/singletons/pairs and FIXING every empty vertex,
        preserves the completion semantics and the pinned empty mask.  hsbK forces the
        rows of empties 7..7+K-1 (their singleton/pair neighbourhoods) to be lex-minimal
        along the stabilizer chain (edge-only clauses).  Sound for the lex-min orbit
        representative in DIMACS edge order.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAT49 = HERE.parent / "sat49"
sys.path.insert(0, str(SAT49))

import check_h7_t0_canonical_completion as canonical  # noqa: E402
import check_h7_t0_canonical_compact as compact  # noqa: E402
import check_h7_t0_copy_quotient as quotient  # noqa: E402

LABEL_PAIRS = list(itertools.combinations(range(7), 2))
PIDX = {p: i for i, p in enumerate(LABEL_PAIRS)}
OUTSIDE = list(range(14, 49))  # singleton + pair-support lows


def roots() -> dict:
    data = json.loads((HERE.parent / "h7-frontier-map-20260915/results.json").read_text())
    return {r["id"]: r for r in data["rows"]}


def labels(v: int) -> tuple[int, ...]:
    if 14 <= v < 28:
        return ((v - 14) // 2,)
    a, b = LABEL_PAIRS[v - 28]
    return (a, b)


def vmap(sig: tuple[int, ...], flips: int, v: int) -> int:
    if v < 7:
        return sig[v]
    if v < 14:
        return v
    if v < 28:
        w, c = divmod(v - 14, 2)
        return 14 + 2 * sig[w] + (c ^ ((flips >> w) & 1))
    a, b = LABEL_PAIRS[v - 28]
    x, y = sig[a], sig[b]
    return 28 + PIDX[(min(x, y), max(x, y))]


def group():
    for sig in itertools.permutations(range(7)):
        for flips in range(128):
            yield (sig, flips)


def row_key(row) -> int:
    # lex order on DIMACS edge bits (e,14) < (e,15) < ... : smaller int = lex-smaller
    return sum(1 << (48 - v) for v in row)


def candidate_rows(size: int):
    out = []

    def rec(start, used, chosen):
        if len(chosen) == size:
            out.append(frozenset(chosen))
            return
        for i in range(start, len(OUTSIDE)):
            v = OUTSIDE[i]
            ls = labels(v)
            if any(l in used for l in ls):
                continue
            rec(i + 1, used | set(ls), chosen + [v])

    rec(0, set(), [])
    return out


def mask_adj(mask: int):
    adj = {e: set() for e in range(7, 14)}
    for idx, (l, r) in enumerate(quotient.EDGES):
        if mask >> idx & 1:
            adj[7 + l].add(7 + r)
            adj[7 + r].add(7 + l)
    return adj


def hsb_clauses(mask: int, depth: int, edge_var, stats: dict):
    """Lex-min stabilizer-chain normalisation of empty rows 7..7+depth-1."""
    adj = mask_adj(mask)
    empties = list(range(7, 7 + depth))
    G = list(group())
    clauses = []
    leaves = []

    def compatible(row, e, prefix):
        for (f, rf) in prefix:
            common_empty = len(adj[e] & adj[f])
            if len(row & rf) + common_empty > 1:
                return False
        return True

    def apply(g, row):
        return frozenset(vmap(g[0], g[1], v) for v in row)

    def prefix_lits(prefix):
        return [-edge_var[(f, v)] for (f, rf) in prefix for v in sorted(rf)]

    # recursion over levels: prefix = list of (empty, row), stab = list of group elems
    def level(k, prefix, stab):
        if k == depth:
            leaves.append(list(prefix))
            stats["leaves"] = stats.get("leaves", 0) + 1
            stats["min_stab"] = min(stats.get("min_stab", 10**9), len(stab))
            stats["max_stab"] = max(stats.get("max_stab", 0), len(stab))
            return
        e = empties[k]
        size = 7 - len(adj[e])
        cands = [r for r in candidate_rows(size) if compatible(r, e, prefix)]
        seen = set()
        canon = []
        for r in sorted(cands, key=row_key):
            if r in seen:
                continue
            orbit = {apply(g, r) for g in stab}
            seen |= orbit
            canon.append(r)  # sorted ascending => first seen is orbit min
        canon_set = set(canon)
        base = prefix_lits(prefix)
        nforb = 0
        for r in cands:
            if r not in canon_set:
                clauses.append(tuple(base + [-edge_var[(e, v)] for v in sorted(r)]))
                nforb += 1
        stats.setdefault(f"level{k}", []).append(
            {"cands": len(cands), "canon": len(canon), "forbidden": nforb, "stab": len(stab)})
        for r in canon:
            sub = [g for g in stab if apply(g, r) == r]
            level(k + 1, prefix + [(e, r)], sub)

    level(0, [], G)
    return clauses, leaves


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True, help="e.g. cube_F9_t0")
    ap.add_argument("--facts", default="", help="comma list: cap,fp,x35,dlex,hsb1,hsb2,...")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--base-cache", type=Path, help="write/read plain cube CNF here")
    ap.add_argument("--sample-leaves", type=int, default=0,
                    help="also write N random hsb leaf cubes (rows fully fixed) as <out>.leafNNN.cnf")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()

    row = roots()[args.root]
    mask, edge_count = row["mask"], row["edge_count"]
    cnf, edge_vars, _ = canonical.build_cnf(compact.CompactCnf)
    for index, (l, r) in enumerate(quotient.EDGES):
        v = edge_vars[(7 + l, 7 + r)]
        cnf.add(v if (mask >> index) & 1 else -v)
    assert cnf.variable_count == 17633 and len(cnf.clauses) == 720825
    lines = [f"p cnf {cnf.variable_count} {len(cnf.clauses)}\n"]
    lines += [" ".join(map(str, c)) + " 0\n" for c in cnf.clauses]
    data = "".join(lines).encode()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == row["cnf_sha256"], (digest, row["cnf_sha256"])
    if args.base_cache:
        args.base_cache.write_bytes(data)

    def ev(a, b):
        return edge_vars[(min(a, b), max(a, b))]

    adj = mask_adj(mask)
    extra: list[tuple[int, ...]] = []
    leaves = []
    top = cnf.variable_count
    stats: dict = {"root": args.root, "mask": mask, "base_sha256": digest}
    facts = [f for f in args.facts.split(",") if f]
    for fact in facts:
        before = len(extra)
        if fact == "cap":
            for s in range(14, 28):
                for t in itertools.combinations(range(7, 14), 3):
                    extra.append(tuple(-ev(s, e) for e in t))
            for p in range(28, 49):
                for t in itertools.combinations(range(7, 14), 2):
                    extra.append(tuple(-ev(p, e) for e in t))
        elif fact == "fp":
            for u, v in itertools.combinations(range(7, 14), 2):
                if adj[u] & adj[v]:
                    for z in OUTSIDE:
                        extra.append((-ev(u, z), -ev(v, z)))
        elif fact == "x35":
            bound = 35 - 4 * edge_count
            ys = []
            for u, v in itertools.combinations(range(7, 14), 2):
                top += 1
                y = top
                ys.append(y)
                cs = []
                for z in OUTSIDE:
                    top += 1
                    c = top
                    cs.append(c)
                    extra.append((-c, ev(u, z)))
                    extra.append((-c, ev(v, z)))
                extra.append(tuple([-y] + cs))
            # at least `bound` of ys  <=>  at most 21-bound of the negations (Sinz)
            lits = [-y for y in ys]
            k = len(lits) - bound
            if bound > 0:
                n = len(lits)
                s = [[0] * (k + 1) for _ in range(n)]
                for i in range(n):
                    for j in range(1, k + 1):
                        top += 1
                        s[i][j] = top
                for i in range(n):
                    extra.append((-lits[i], s[i][1]))
                    if i > 0:
                        for j in range(1, k + 1):
                            extra.append((-s[i - 1][j], s[i][j]))
                        for j in range(2, k + 1):
                            extra.append((-lits[i], -s[i - 1][j - 1], s[i][j]))
                        extra.append((-lits[i], -s[i - 1][k]))
            stats["x35_bound"] = bound
        elif fact == "dlex":
            import generate_h7_empty_cube_stabilizer_lex as lex
            grp = lex.stabilizer(mask)
            for perm in grp:
                if perm == tuple(range(7)):
                    continue
                enc, nxt = lex.lex_leader_clauses(lex.edge_variable_permutation(perm), top + 1)
                extra.extend(enc)
                top = nxt - 1
            stats["dlex_stabilizer"] = len(grp)
        elif fact.startswith("hsb"):
            depth = int(fact[3:])
            hs: dict = {}
            cl, leaves = hsb_clauses(mask, depth, {(e, v): ev(e, v) for e in range(7, 14) for v in OUTSIDE}, hs)
            extra.extend(cl)
            stats["hsb"] = {k: v for k, v in hs.items() if not k.startswith("level")}
            stats["hsb_levels"] = {k: [len(v), sum(x["forbidden"] for x in v)] for k, v in hs.items() if k.startswith("level")}
        else:
            raise SystemExit(f"unknown fact {fact}")
        stats[f"clauses_{fact}"] = len(extra) - before
    with args.out.open("wb") as fh:
        fh.write(f"p cnf {top} {len(cnf.clauses) + len(extra)}\n".encode())
        fh.write(data[data.index(b"\n") + 1:])
        for c in extra:
            fh.write((" ".join(map(str, c)) + " 0\n").encode())
    if args.sample_leaves and leaves:
        import random
        rng = random.Random(args.seed)
        picks = rng.sample(range(len(leaves)), min(args.sample_leaves, len(leaves)))
        body = args.out.read_bytes()
        body = body[body.index(b"\n") + 1:]
        for n, li in enumerate(picks):
            units = []
            for (e, r) in leaves[li]:
                units += [(ev(e, v) if v in r else -ev(e, v)) for v in OUTSIDE]
            with open(f"{args.out}.leaf{n:03d}.cnf", "wb") as fh:
                fh.write(f"p cnf {top} {len(cnf.clauses) + len(extra) + len(units)}\n".encode())
                fh.write(body)
                fh.write("".join(f"{u} 0\n" for u in units).encode())
        stats["leaf_picks"] = picks
    stats["variables"] = top
    stats["clauses"] = len(cnf.clauses) + len(extra)
    stats["sha256"] = hashlib.sha256(args.out.read_bytes()).hexdigest()
    print(json.dumps(stats, sort_keys=True, default=str))


if __name__ == "__main__":
    main()
