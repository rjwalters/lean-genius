#!/usr/bin/env python3
"""
Bounded witness search for the Fermat defect-one conjecture at n = 4.

Searches for a primitive nontrivial witness (a, b, c) with
    2 <= a <= b < c <= N    and    |a^4 + b^4 - c^4| = 1.
The Nat-disjunction form (matching FermatDefectWitness in
proofs/Proofs/FermatDefectOne.lean) is:
    a^4 + b^4 + 1 = c^4   (negative defect, a^4+b^4-c^4 = -1)
    a^4 + b^4     = c^4 + 1 (positive defect, a^4+b^4-c^4 = +1)

Two independent methods are run:
  (1) fast: hash perfect fourth powers, solve for b given (a, c);
  (2) brute: triple-nested loop, no hash trick (cross-check).

Issue #22635. Run directly with `python3 witness_search_n4_bound1000.py`.
"""
from math import gcd

N = 1000
n = 4


def fast_search():
    p4 = [i ** 4 for i in range(N + 1)]
    pow4_to_b = {p4[b]: b for b in range(2, N + 1)}
    witnesses = []
    pairs = 0
    for c in range(3, N + 1):
        c4 = p4[c]
        for a in range(2, c):
            a4 = p4[a]
            # negative defect: b^4 = c^4 - a^4 - 1
            tneg = c4 - a4 - 1
            b = pow4_to_b.get(tneg)
            if b is not None and a <= b < c:
                witnesses.append((a, b, c, "neg", gcd(gcd(a, b), c)))
            # positive defect: b^4 = c^4 + 1 - a^4
            tpos = c4 + 1 - a4
            b = pow4_to_b.get(tpos)
            if b is not None and a <= b < c:
                witnesses.append((a, b, c, "pos", gcd(gcd(a, b), c)))
            pairs += 1
    return witnesses, pairs


def brute_search():
    witnesses = []
    for c in range(3, N + 1):
        c4 = c ** 4
        for a in range(2, c):
            a4 = a ** 4
            for b in range(a, c):
                d = a4 + b ** 4 - c4
                if d in (1, -1):
                    witnesses.append((a, b, c, d, gcd(gcd(a, b), c)))
    return witnesses


def modular_filter_report():
    """No single small modulus obstructs a^4+b^4 -/+ 1 = c^4 (the +/-1 is
    absorbed by the residue 1 = 1^4). Reported for completeness."""
    def fourth_residues(p):
        return set((x ** 4) % p for x in range(p))
    out = []
    for p in [3, 5, 7, 13, 16]:
        r = fourth_residues(p)
        sums = set((x + y) % p for x in r for y in r)
        neg_ok = any(((s + 1) % p) in r for s in sums)
        pos_ok = any(((s - 1) % p) in r for s in sums)
        out.append((p, sorted(r), neg_ok, pos_ok))
    return out


if __name__ == "__main__":
    fast, pairs = fast_search()
    print(f"[fast]  (a,c) pairs iterated: {pairs}")
    print(f"[fast]  witnesses |defect|=1 (any gcd): {len(fast)}")
    for w in fast:
        print("       ", w)
    prim = [w for w in fast if w[4] == 1]
    print(f"[fast]  primitive witnesses (gcd=1): {len(prim)}")

    brute = brute_search()
    print(f"[brute] witnesses |defect|=1 (any gcd): {len(brute)}")

    assert len(fast) == len(brute), "method mismatch!"
    print("[ok]    fast and brute agree.")

    print("\nModular pre-filter (no single small modulus obstructs):")
    for p, res, neg, pos in modular_filter_report():
        print(f"  mod {p:>2}: 4th-power residues={res}  neg-solvable={neg}  pos-solvable={pos}")
